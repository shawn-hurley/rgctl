//! Complete receiver producers with balanced, explicit invocation contexts.
//! The merged possible-origin graph is unchanged. Missing/recursive/partial
//! producers decline a refinement instead of proving an absent target.
use crate::{
    call_bindings::{
        BindingSource, CallBindings, CallRef, InvocationTarget, TransferKind, ValueRef,
    },
    interprocedural_cfg::InterproceduralCfgAccess,
    local_value_flow::{LocalFlowDiagnostic, LocalValueFlow},
    operands::*,
    pdg::ProgramDependenceGraph,
    receiver_closure::ResolvedConstruction,
    receiver_program::ProgramClosedReceiver,
    value_origins::OriginLimits,
};
use std::collections::{BTreeSet, HashMap, HashSet};
use uuid::Uuid;

/// Immutable native local flow and resolver-qualified direct bindings, reusable
/// across entrypoint queries. There is no per-query source parsing or graph clone.
pub struct ContextReceiverProgram {
    local: HashMap<ValueRef, Vec<ValueRef>>,
    bad: HashSet<ValueRef>,
    bad_functions: HashSet<Uuid>,
    roots: HashMap<ValueRef, BTreeSet<Uuid>>,
    formals: HashMap<(InvocationTarget, ValueRef), Vec<ValueRef>>,
    returns: HashMap<InvocationTarget, Vec<(ValueRef, ValueRef)>>,
    targets: HashMap<CallRef, Vec<InvocationTarget>>,
    invalid: HashSet<InvocationTarget>,
    /// Exhausted construction limits prohibit all exclusions.
    pub limited: bool,
}
impl ContextReceiverProgram {
    /// `roots` must be exactly resolved allocations, not possible-origin seeds.
    /// `targets` must enumerate every possible target of each admitted direct
    /// invocation. Unresolved and indirect calls must not be represented as a
    /// complete singleton merely because one possible target was found.
    pub fn build<C: InterproceduralCfgAccess + ?Sized>(
        icfg: &C,
        functions: &[Uuid],
        roots: &[ResolvedConstruction],
        targets: &[InvocationTarget],
        limits: OriginLimits,
    ) -> Self {
        let mut out = Self {
            local: HashMap::new(),
            bad: HashSet::new(),
            bad_functions: HashSet::new(),
            roots: HashMap::new(),
            formals: HashMap::new(),
            returns: HashMap::new(),
            targets: HashMap::new(),
            invalid: HashSet::new(),
            limited: false,
        };
        if functions.len() > limits.max_functions
            || roots.len() > limits.max_facts
            || targets.len() > limits.max_targets
        {
            out.limited = true;
            return out;
        }
        let mut records = 0usize;
        let mut transfers = 0usize;
        for &function in functions {
            let Some(cfg) = icfg.get_cfg(function) else {
                out.bad_functions.insert(function);
                continue;
            };
            records = records.saturating_add(cfg.operands.expressions.len());
            if records > limits.max_facts {
                out.limited = true;
                return out;
            }
            if cfg.operands.status != OperandStatus::Captured
                || !cfg.operands.valid_references()
                || cfg
                    .operands
                    .diagnostics
                    .iter()
                    .any(|d| d.kind != OperandDiagnosticKind::NestedCallable)
            {
                out.bad_functions.insert(function);
                continue;
            }
            let Ok(pdg) = ProgramDependenceGraph::build(cfg, &[]) else {
                out.bad_functions.insert(function);
                continue;
            };
            let local = LocalValueFlow::build(cfg, &pdg, limits.local);
            for diagnostic in local.diagnostics {
                match diagnostic {
                    LocalFlowDiagnostic::UnboundRead(e)
                    | LocalFlowDiagnostic::UnmodeledWrite(e)
                    | LocalFlowDiagnostic::AmbiguousOccurrence(e)
                    | LocalFlowDiagnostic::IntraStatementWrites(e) => {
                        out.bad.insert(ValueRef {
                            function,
                            expression: e,
                        });
                    }
                    LocalFlowDiagnostic::PartialOperands => {}
                    _ => {
                        out.bad_functions.insert(function);
                    }
                }
            }
            for t in local.transfers {
                transfers = transfers.saturating_add(1);
                if transfers > limits.max_transfers {
                    out.limited = true;
                    return out;
                }
                out.local
                    .entry(ValueRef {
                        function,
                        expression: t.to,
                    })
                    .or_default()
                    .push(ValueRef {
                        function,
                        expression: t.from,
                    });
            }
        }
        for root in roots {
            out.roots
                .entry(root.value)
                .or_default()
                .insert(root.type_id);
        }
        let mut bindings = CallBindings::new(icfg);
        for &target in targets {
            out.targets.entry(target.call).or_default().push(target);
            let Ok(binding) = bindings.bind(target) else {
                out.invalid.insert(target);
                continue;
            };
            if binding.diagnostics.len != 0 {
                out.invalid.insert(target);
                continue;
            }
            for transfer in binding.transfers.slice(bindings.transfers()).unwrap_or(&[]) {
                transfers = transfers.saturating_add(1);
                if transfers > limits.max_transfers {
                    out.limited = true;
                    return out;
                }
                let BindingSource::Expression(from) = transfer.from else {
                    out.invalid.insert(target);
                    continue;
                };
                match transfer.kind {
                    TransferKind::ActualToFormal
                    | TransferKind::ReceiverToFormal
                    | TransferKind::DefaultToFormal { .. } => {
                        out.formals
                            .entry((target, transfer.to))
                            .or_default()
                            .push(from);
                    }
                    TransferKind::ReturnToResult { position: 0 } => {
                        out.returns
                            .entry(target)
                            .or_default()
                            .push((from, transfer.to));
                    }
                    _ => {
                        out.invalid.insert(target);
                    }
                }
            }
        }
        for targets in out.targets.values_mut() {
            targets.sort_by_key(|t| (t.callee, t.call.caller, t.call.site.0));
            targets.dedup();
        }
        out
    }
    /// Complete receiver types in `function` under this exact balanced call path.
    /// An empty path has no incoming formal assumptions. Invalid paths, missing
    /// producers, cycles, and depth/step exhaustion return no qualified receivers.
    pub fn receivers<C: InterproceduralCfgAccess + ?Sized>(
        &self,
        icfg: &C,
        function: Uuid,
        context: &[InvocationTarget],
        max_steps: usize,
    ) -> Vec<ProgramClosedReceiver> {
        if self.limited
            || context.len() > 32
            || context.last().is_some_and(|t| t.callee != function)
            || context.windows(2).any(|p| p[0].callee != p[1].call.caller)
            || context.iter().any(|t| {
                self.invalid.contains(t)
                    || !self.targets.get(&t.call).is_some_and(|v| v.contains(t))
            })
        {
            return vec![];
        }
        let Some(cfg) = icfg.get_cfg(function) else {
            return vec![];
        };
        let mut remaining = max_steps;
        let mut out = Vec::new();
        for (site, call) in cfg.operands.calls.iter().enumerate() {
            let Some(receiver) = call.receiver else {
                continue;
            };
            let mut active = HashSet::new();
            if let Some((types, allocations)) = self.producers(
                icfg,
                ValueRef {
                    function,
                    expression: receiver,
                },
                context,
                &mut remaining,
                &mut active,
            ) {
                if !types.is_empty() {
                    out.push(ProgramClosedReceiver {
                        call: CallRef {
                            caller: function,
                            site: CallSiteId(site as u32),
                        },
                        types: types.into_iter().collect(),
                        allocations: {
                            let mut v: Vec<_> = allocations.into_iter().collect();
                            v.sort_by_key(|v| (v.function, v.expression.0));
                            v
                        },
                    });
                }
            }
            if remaining == 0 {
                return vec![];
            }
        }
        out
    }
    fn producers<C: InterproceduralCfgAccess + ?Sized>(
        &self,
        icfg: &C,
        value: ValueRef,
        context: &[InvocationTarget],
        remaining: &mut usize,
        active: &mut HashSet<(ValueRef, Vec<InvocationTarget>)>,
    ) -> Option<(BTreeSet<Uuid>, HashSet<ValueRef>)> {
        *remaining = remaining.checked_sub(1)?;
        if context.len() > 32 || active.len() > 256 || self.bad_functions.contains(&value.function)
        {
            return None;
        }
        let key = (value, context.to_vec());
        if !active.insert(key.clone()) {
            return None;
        }
        let result = self.visit(icfg, value, context, remaining, active);
        active.remove(&key);
        result
    }
    fn visit<C: InterproceduralCfgAccess + ?Sized>(
        &self,
        icfg: &C,
        value: ValueRef,
        context: &[InvocationTarget],
        remaining: &mut usize,
        active: &mut HashSet<(ValueRef, Vec<InvocationTarget>)>,
    ) -> Option<(BTreeSet<Uuid>, HashSet<ValueRef>)> {
        if let Some(types) = self.roots.get(&value) {
            return Some((types.clone(), HashSet::from([value])));
        }
        if self.bad.contains(&value) {
            return None;
        }
        let cfg = icfg.get_cfg(value.function)?;
        let expression = cfg.operands.expressions.get(value.expression.0 as usize)?;
        let mut predecessors = Vec::new();
        match expression.kind {
            ExpressionKind::Formal(_) => {
                let frame = *context.last()?;
                if frame.callee != value.function || self.invalid.contains(&frame) {
                    return None;
                }
                for &from in self.formals.get(&(frame, value))? {
                    let parent = if from.function == value.function {
                        context.to_vec()
                    } else {
                        context[..context.len() - 1].to_vec()
                    };
                    predecessors.push((from, parent));
                }
            }
            ExpressionKind::CallResult(site) => {
                let targets = self.targets.get(&CallRef {
                    caller: value.function,
                    site,
                })?;
                for &target in targets {
                    if self.invalid.contains(&target) {
                        return None;
                    }
                    let returns = self.returns.get(&target)?;
                    let mut matched = false;
                    for &(from, to) in returns.iter().filter(|(_, to)| *to == value) {
                        let mut child = context.to_vec();
                        child.push(target);
                        predecessors.push((from, child));
                        matched = true;
                        let _ = to;
                    }
                    if !matched {
                        return None;
                    }
                }
            }
            ExpressionKind::Name(_)
            | ExpressionKind::Parenthesized
            | ExpressionKind::AssertedValue
            | ExpressionKind::Conditional { .. } => {
                predecessors.extend(
                    self.local
                        .get(&value)?
                        .iter()
                        .map(|&from| (from, context.to_vec())),
                );
            }
            _ => return None,
        }
        if predecessors.is_empty() {
            return None;
        }
        let mut types = BTreeSet::new();
        let mut allocations = HashSet::new();
        for (from, path) in predecessors {
            let (t, a) = self.producers(icfg, from, &path, remaining, active)?;
            types.extend(t);
            allocations.extend(a);
        }
        Some((types, allocations))
    }
}

/// Source-native class declarations whose default construction has no user
/// constructor, fields, decorators, dynamic attribute hooks, or unknown bases.
/// Import/name resolution and mutation/escape guards remain caller premises.
/// This supports a deliberately narrow nominal root for JS/Python context queries.
pub fn simple_nominal_classes(
    parsed: &crate::cfg_builder::ParsedSourceFile,
    language: &str,
    source: &[u8],
) -> Vec<OperandSpan> {
    if !matches!(language, "javascript" | "python") {
        return vec![];
    }
    let root = parsed.tree().root_node();
    let mut classes = Vec::new();
    let mut stack = vec![root];
    let mut visited = 0;
    while let Some(n) = stack.pop() {
        visited += 1;
        if visited > 1_000_000 {
            return vec![];
        }
        if matches!(n.kind(), "class_declaration" | "class_definition") {
            classes.push(n);
        }
        let mut c = n.walk();
        stack.extend(n.named_children(&mut c));
    }
    let protocol = root.named_children(&mut root.walk()).any(|n| {
        n.kind() == "import_from_statement"
            && n.child_by_field_name("module_name")
                .and_then(|n| n.utf8_text(source).ok())
                == Some("typing")
            && n.named_children(&mut n.walk())
                .any(|n| n.kind() == "dotted_name" && n.utf8_text(source).ok() == Some("Protocol"))
    });
    fn simple(
        node: tree_sitter::Node<'_>,
        language: &str,
        source: &[u8],
        classes: &[tree_sitter::Node<'_>],
        protocol: bool,
        active: &mut HashSet<usize>,
    ) -> bool {
        if !active.insert(node.id()) || active.len() > 64 {
            return false;
        }
        let result = (|| {
            if node
                .parent()
                .is_some_and(|n| n.kind() == "decorated_definition")
            {
                return false;
            }
            if language == "javascript"
                && node
                    .named_children(&mut node.walk())
                    .any(|n| matches!(n.kind(), "class_heritage" | "decorator"))
            {
                return false;
            }
            if language == "python"
                && let Some(bases) = node.child_by_field_name("superclasses")
            {
                for base in bases.named_children(&mut bases.walk()) {
                    if base.kind() != "identifier" {
                        return false;
                    }
                    let Ok(name) = base.utf8_text(source) else {
                        return false;
                    };
                    if name == "Protocol" && protocol {
                        continue;
                    }
                    let candidates: Vec<_> = classes
                        .iter()
                        .filter(|n| {
                            n.child_by_field_name("name")
                                .and_then(|n| n.utf8_text(source).ok())
                                == Some(name)
                        })
                        .collect();
                    if candidates.len() != 1
                        || !simple(*candidates[0], language, source, classes, protocol, active)
                    {
                        return false;
                    }
                }
            }
            let Some(body) = node.child_by_field_name("body") else {
                return false;
            };
            for member in body.named_children(&mut body.walk()) {
                if matches!(member.kind(), "comment" | "pass_statement") {
                    continue;
                }
                if language == "python"
                    && member.kind() == "expression_statement"
                    && member.named_child(0).is_some_and(|n| n.kind() == "string")
                {
                    continue;
                }
                if !matches!(member.kind(), "method_definition" | "function_definition") {
                    return false;
                }
                if member
                    .children(&mut member.walk())
                    .any(|n| matches!(n.kind(), "get" | "set"))
                {
                    return false;
                }
                let Some(name) = member.child_by_field_name("name") else {
                    return false;
                };
                if !matches!(name.kind(), "identifier" | "property_identifier") {
                    return false;
                }
                if language == "python" && name.utf8_text(source).is_ok_and(|n| n.starts_with("__"))
                {
                    return false;
                }
                if matches!(
                    name.utf8_text(source).ok(),
                    Some(
                        "constructor" | "__init__" | "__new__" | "__getattribute__" | "__getattr__"
                    )
                ) {
                    return false;
                }
            }
            true
        })();
        active.remove(&node.id());
        result
    }
    classes
        .iter()
        .filter(|n| {
            simple(
                **n,
                language,
                source,
                &classes,
                protocol,
                &mut HashSet::new(),
            )
        })
        .filter_map(|n| {
            Some(OperandSpan {
                start: u32::try_from(n.start_byte()).ok()?,
                end: u32::try_from(n.end_byte()).ok()?,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        call_bindings::ReceiverSupply, cfg_builder::build_cfg_for_function,
        interprocedural_cfg::InterproceduralCFG,
    };
    use rgctl_graph::{
        backend::{GraphBackend, MemoryBackend},
        schema::{Node, NodeType},
    };
    fn label(o: &FunctionOperands, e: ExpressionId) -> Option<&str> {
        match o.expressions[e.0 as usize].kind {
            ExpressionKind::Name(n) | ExpressionKind::Member(n) => o.name(n),
            _ => None,
        }
    }
    #[test]
    fn selected_caller_arguments_do_not_merge_with_sibling_callers_in_five_languages() {
        for (language, source) in [
            (
                "java",
                "class App{static int consume(Y value){return value.execute();}static int exercise(){return consume(new W());}static int other(){return consume(new X());}}",
            ),
            (
                "javascript",
                "function consume(value){return value.execute();}function exercise(){return consume(new W());}function other(){return consume(new X());}",
            ),
            (
                "typescript",
                "function consume(value:Y){return value.execute();}function exercise(){return consume(new W());}function other(){return consume(new X());}",
            ),
            (
                "python",
                "def consume(value):\n return value.execute()\ndef exercise():\n return consume(W())\ndef other():\n return consume(X())\n",
            ),
            (
                "go",
                "package p\nfunc consume(value Y)int{return value.Execute()}\nfunc exercise()int{return consume(W{})}\nfunc other()int{return consume(X{})}",
            ),
        ] {
            let names = ["consume", "exercise", "other"];
            let mut cfgs = HashMap::new();
            let mut graph = MemoryBackend::new();
            for (i, name) in names.iter().enumerate() {
                let id = Uuid::from_u128(i as u128 + 1);
                cfgs.insert(id, build_cfg_for_function(language, source, name).unwrap());
                let mut n = Node::new(NodeType::Function, *name);
                n.id = id;
                graph.insert_node(n).unwrap();
            }
            let mut roots = Vec::new();
            let mut targets = Vec::new();
            for (&function, cfg) in &cfgs {
                for (i, c) in cfg.operands.calls.iter().enumerate() {
                    if let Some(n @ ("W" | "X")) = label(&cfg.operands, c.callee) {
                        roots.push(ResolvedConstruction {
                            value: ValueRef {
                                function,
                                expression: c.result,
                            },
                            type_id: Uuid::from_u128(if n == "W" { 101 } else { 100 }),
                        });
                    }
                    if label(&cfg.operands, c.callee) == Some("consume") {
                        targets.push(InvocationTarget {
                            call: CallRef {
                                caller: function,
                                site: CallSiteId(i as u32),
                            },
                            callee: Uuid::from_u128(1),
                            receiver: ReceiverSupply::None,
                        });
                    }
                }
                for (i, e) in cfg.operands.expressions.iter().enumerate() {
                    if let ExpressionKind::Construction(head) = e.kind
                        && let Some(n @ ("W" | "X")) = label(&cfg.operands, head)
                    {
                        roots.push(ResolvedConstruction {
                            value: ValueRef {
                                function,
                                expression: ExpressionId(i as u32),
                            },
                            type_id: Uuid::from_u128(if n == "W" { 101 } else { 100 }),
                        });
                    }
                }
            }
            let icfg = InterproceduralCFG::from_cfg_archive(&graph, cfgs).unwrap();
            let functions = icfg.function_cfgs.keys().copied().collect::<Vec<_>>();
            let exhausted = ContextReceiverProgram::build(
                &icfg,
                &functions,
                &roots,
                &targets,
                OriginLimits {
                    max_transfers: 0,
                    ..Default::default()
                },
            );
            assert!(
                exhausted.limited,
                "{language}: local transfers must share the global budget"
            );
            assert!(
                exhausted
                    .receivers(&icfg, Uuid::from_u128(1), &[], 10000)
                    .is_empty()
            );
            let program = ContextReceiverProgram::build(
                &icfg,
                &functions,
                &roots,
                &targets,
                OriginLimits::default(),
            );
            assert!(
                program
                    .receivers(&icfg, Uuid::from_u128(1), &[], 10000)
                    .is_empty()
            );
            for target in &targets {
                let result = program.receivers(&icfg, target.callee, &[*target], 10000);
                assert_eq!(result.len(), 1, "{language}, {target:?}");
                assert_eq!(
                    result[0].types,
                    vec![Uuid::from_u128(
                        if target.call.caller == Uuid::from_u128(2) {
                            101
                        } else {
                            100
                        }
                    )],
                    "{language}"
                );
                assert!(
                    program
                        .receivers(&icfg, target.callee, &[*target], 0)
                        .is_empty()
                );
            }
        }
    }
    #[test]
    fn nominal_class_guards_reject_custom_construction_and_dynamic_dispatch() {
        for (language, source, count) in [
            (
                "javascript",
                "class W{execute(){return 200}} class Bad{constructor(){return new X()}}",
                1,
            ),
            (
                "python",
                "from typing import Protocol\nclass Y(Protocol):\n def execute(self): ...\nclass W(Y):\n def execute(self):return 200\nclass Bad:\n def __new__(cls):return X()\n",
                2,
            ),
            (
                "python",
                "@decorator\nclass W:\n def execute(self):return 200\n",
                0,
            ),
        ] {
            let parsed =
                crate::cfg_builder::ParsedSourceFile::parse(language, source.as_bytes()).unwrap();
            assert_eq!(
                simple_nominal_classes(&parsed, language, source.as_bytes()).len(),
                count,
                "{language}"
            );
        }
    }
}
