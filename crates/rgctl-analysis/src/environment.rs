//! Native lexical binding links between separately lowered procedures.
//! Source is indexed through the cached tree; the origin query consumes only facts.
use crate::call_bindings::ValueRef;
use crate::cfg_builder::ParsedSourceFile;
use crate::operands::*;
use rgctl_error::{Error, Result};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use tree_sitter::Node;
use uuid::Uuid;

#[path = "java_fields.rs"]
mod java_fields;

#[path = "environment_program.rs"]
mod program;
pub use program::{
    EnvironmentExport, EnvironmentExternalRead, EnvironmentExternalStore, EnvironmentModule,
    link_environment_modules,
};

/// A declaration-qualified storage identity, independent of its read spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EnvironmentBinding {
    /// Owning module or procedure in this immutable analysis revision.
    pub owner: Uuid,
    /// Canonical first declaration in the lexical scope.
    pub declaration: OperandSpan,
}
/// One possible store/read dependency across procedure environments.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct EnvironmentTransfer {
    /// Canonical owning declaration.
    pub binding: EnvironmentBinding,
    /// Parameter entry or explicit initializer/assignment value.
    pub from: ValueRef,
    /// Exact native reference to this binding.
    pub to: ValueRef,
}
/// An implicit Java member read resolved to its native receiver.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvironmentMemberRead {
    /// Function-qualified this value.
    pub receiver: ValueRef,
    /// Canonical declared member's name, scoped by the receiver object.
    pub member: String,
    /// Bare field reference requiring a member load.
    pub value: ValueRef,
}
/// A native literal/definition expression whose body has a separate graph identity.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct EnvironmentCallable {
    /// Callable creation/definition value in its enclosing procedure.
    pub value: ValueRef,
    /// Canonical separately lowered body.
    pub callee: Uuid,
}
/// Missing environment coverage; none of these means absence of impact.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EnvironmentDiagnostic {
    /// No visible source declaration was established for this native read.
    UnresolvedRead {
        /// Exact native read expression.
        value: ValueRef,
        /// Unresolved source name.
        name: String,
    },
    /// A declaration was found but no modeled parameter/initializer/store supplies it.
    MissingProducer(EnvironmentBinding),
    /// A static field has an assignment whose RHS was not captured. Known
    /// producers remain possible, but cannot support a complete exclusion.
    IncompleteStorage(EnvironmentBinding),
    /// An implicit member needs a receiver not supplied by this procedure.
    MissingMemberReceiver(ValueRef),
    /// Literal syntax had no prepared canonical callable body/identity.
    MissingCallableDefinition(OperandSpan),
    /// Syntax/declaration/link/candidate budget was exhausted.
    LimitReached,
    /// A source import/package binding had no modeled source export.
    UnresolvedImport {
        /// Native consumer reference.
        value: ValueRef,
        /// Source module/package spelling.
        module: String,
        /// Imported declaration/member name.
        name: String,
    },
}
/// Native query-local environment facts; no source parsing occurs in the solver.
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct EnvironmentFacts {
    /// Module-level producers available to canonical import/package linking.
    pub exports: Vec<EnvironmentExport>,
    /// Imported or same-package reads requiring program-level linking.
    pub external_reads: Vec<EnvironmentExternalRead>,
    /// Qualified static-field assignments, resolved with the complete source inventory.
    #[serde(default)]
    pub external_stores: Vec<EnvironmentExternalStore>,
    /// Go package clause, when present, for directory-qualified package identity.
    pub package_name: Option<String>,
    /// Possible stores joined to reads by owning binding.
    pub transfers: Vec<EnvironmentTransfer>,
    /// Explicit receiver-qualified field loads for bare member reads.
    pub member_reads: Vec<EnvironmentMemberRead>,
    /// Definition/literal values tied to canonical callable bodies.
    pub callables: Vec<EnvironmentCallable>,
    /// Partial or missing coverage evidence.
    pub diagnostics: Vec<EnvironmentDiagnostic>,
}
/// One prepared procedure, including the module initializer record.
pub struct EnvironmentProcedure<'a> {
    /// Canonical function or query-local module UUID.
    pub id: Uuid,
    /// Native operands from the same cached tree and source revision.
    pub operands: &'a FunctionOperands,
}
/// Bounded source indexing and cross-procedure joins.
#[derive(Debug, Clone, Copy)]
pub struct EnvironmentLimits {
    /// Maximum inspected syntax nodes.
    pub max_nodes: usize,
    /// Maximum declaration/write records.
    pub max_declarations: usize,
    /// Maximum reference candidates and emitted links.
    pub max_checks: usize,
}
impl Default for EnvironmentLimits {
    fn default() -> Self {
        Self {
            max_nodes: 1_000_000,
            max_declarations: 50_000,
            max_checks: 250_000,
        }
    }
}
#[derive(Clone)]
struct Declaration {
    name: String,
    scope: OperandSpan,
    owner: Uuid,
    at: OperandSpan,
    field: bool,
    class: Option<OperandSpan>,
}
struct Write {
    name: String,
    at: OperandSpan,
    rhs: OperandSpan,
    owner: Uuid,
    declare: bool,
    scope: OperandSpan,
    field: bool,
    class: Option<OperandSpan>,
}
fn span(node: Node<'_>) -> Result<OperandSpan> {
    Ok(OperandSpan {
        start: u32::try_from(node.start_byte())
            .map_err(|_| Error::SerdeError("environment source exceeds u32".into()))?,
        end: u32::try_from(node.end_byte())
            .map_err(|_| Error::SerdeError("environment source exceeds u32".into()))?,
    })
}
fn contains(outer: OperandSpan, inner: OperandSpan) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}
fn children(node: Node<'_>) -> Vec<Node<'_>> {
    node.named_children(&mut node.walk()).collect()
}
fn is_class(kind: &str) -> bool {
    matches!(
        kind,
        "class_declaration"
            | "class_definition"
            | "class_body"
            | "interface_declaration"
            | "interface_body"
            | "enum_declaration"
            | "enum_body"
            | "record_declaration"
    )
}
fn is_block(kind: &str) -> bool {
    matches!(kind, "block" | "statement_block" | "compound_statement")
}
fn procedure_owner(node: Node<'_>, ids: &HashMap<OperandSpan, Uuid>, module: Uuid) -> Uuid {
    let mut field = Some(node);
    while let Some(n) = field {
        if matches!(n.kind(), "field_declaration" | "constant_declaration") {
            if rgctl_plugin_helpers::java::is_static(n) {
                let mut class = n.parent();
                while let Some(c) = class {
                    if matches!(
                        c.kind(),
                        "class_declaration"
                            | "interface_declaration"
                            | "enum_declaration"
                            | "record_declaration"
                    ) {
                        if let Ok(s) = span(c)
                            && let Some(&id) = ids.get(&s)
                        {
                            return id;
                        }
                        break;
                    }
                    class = c.parent();
                }
            }
            break;
        }
        if ids.contains_key(&span(n).unwrap_or(OperandSpan { start: 0, end: 0 })) {
            break;
        }
        field = n.parent();
    }
    let mut at = Some(node);
    while let Some(n) = at {
        if n.parent().is_some()
            && let Ok(s) = span(n)
            && let Some(&id) = ids.get(&s)
        {
            return id;
        }
        at = n.parent();
    }
    module
}
fn nearest_class(node: Node<'_>) -> Option<OperandSpan> {
    let mut at = node.parent();
    while let Some(n) = at {
        if matches!(
            n.kind(),
            "class_declaration"
                | "class_definition"
                | "interface_declaration"
                | "enum_declaration"
                | "record_declaration"
        ) {
            return span(n).ok();
        }
        at = n.parent();
    }
    None
}
fn lexical_scope(
    node: Node<'_>,
    language: &str,
    function_scoped: bool,
    ids: &HashMap<OperandSpan, Uuid>,
    root: OperandSpan,
) -> (OperandSpan, bool) {
    let mut at = node.parent();
    while let Some(n) = at {
        let s = span(n).unwrap_or(root);
        if is_class(n.kind()) {
            return (s, true);
        }
        if n.parent().is_none() {
            return (root, false);
        }
        if ids.contains_key(&s) {
            return (s, false);
        }
        if language != "python" && !function_scoped && is_block(n.kind()) {
            return (s, false);
        }
        at = n.parent();
    }
    (root, false)
}
fn resolve<'a>(
    name: &str,
    at: OperandSpan,
    language: &str,
    decls: &'a [Declaration],
    by_name: &HashMap<String, Vec<usize>>,
    checks: &mut usize,
    limit: usize,
) -> Option<&'a Declaration> {
    let mut best: Option<&Declaration> = None;
    for &i in by_name.get(name).into_iter().flatten() {
        if *checks >= limit {
            return None;
        }
        *checks += 1;
        let d = &decls[i];
        if d.field && language != "java" {
            continue;
        }
        if contains(d.scope, at)
            && best.is_none_or(|old| {
                (d.scope.end - d.scope.start, d.at.start)
                    < (old.scope.end - old.scope.start, old.at.start)
            })
        {
            best = Some(d)
        }
    }
    best
}
impl ParsedSourceFile {
    /// Resolve local/module/enclosing bindings using the cached native parse.
    /// Procedures and module must belong to these exact source bytes. Caller
    /// contexts and captured cells merge; no closure-instance exclusion is claimed.
    pub fn environment_facts(
        &self,
        language: &str,
        source: &[u8],
        module: Uuid,
        procedures: &[EnvironmentProcedure<'_>],
        limits: EnvironmentLimits,
    ) -> Result<EnvironmentFacts> {
        let root = self.tree().root_node();
        let root_span = span(root)?;
        let ids: HashMap<_, _> = procedures
            .iter()
            .filter(|p| p.id != module)
            .filter_map(|p| p.operands.span.map(|s| (s, p.id)))
            .collect();
        let mut output = EnvironmentFacts::default();
        let imported = program::imports(root, source, language, &ids, limits.max_nodes)?;
        output.package_name = children(root)
            .into_iter()
            .find(|n| n.kind() == "package_clause")
            .and_then(|n| n.named_child(0))
            .and_then(|n| n.utf8_text(source).ok())
            .map(str::to_owned);

        let mut decls = Vec::new();
        let mut writes = Vec::new();
        let mut seen = HashSet::new();
        let mut stack = vec![root];
        let mut nodes = 0usize;
        // Python directives choose an existing cell/module binding, never a new local.
        let mut directives: HashMap<(Uuid, String), bool> = HashMap::new();
        while let Some(node) = stack.pop() {
            nodes += 1;
            if nodes > limits.max_nodes {
                output.diagnostics.push(EnvironmentDiagnostic::LimitReached);
                break;
            }
            if matches!(node.kind(), "global_statement" | "nonlocal_statement") {
                let owner = procedure_owner(node, &ids, module);
                for name in children(node)
                    .into_iter()
                    .filter(|n| n.kind() == "identifier")
                {
                    directives.insert(
                        (owner, name.utf8_text(source)?.to_owned()),
                        node.kind() == "global_statement",
                    );
                }
            }
            stack.extend(children(node));
        }
        for p in procedures {
            if p.id == module {
                continue;
            }
            let Some(scope) = p.operands.span else {
                continue;
            };
            for f in &p.operands.formals {
                let Some(at) = p
                    .operands
                    .expressions
                    .get(f.value.0 as usize)
                    .and_then(|e| e.span)
                else {
                    continue;
                };
                let Some(name) = p.operands.name(f.name) else {
                    continue;
                };
                let scope = if matches!(language, "go" | "java") {
                    root.named_descendant_for_byte_range(scope.start as usize, scope.end as usize)
                        .and_then(|n| n.child_by_field_name("body"))
                        .and_then(|n| span(n).ok())
                        .unwrap_or(scope)
                } else {
                    scope
                };
                decls.push(Declaration {
                    name: name.into(),
                    scope,
                    owner: p.id,
                    at,
                    field: false,
                    class: None,
                });
            }
        }
        stack = vec![root];
        nodes = 0;
        while let Some(node) = stack.pop() {
            nodes += 1;
            if nodes > limits.max_nodes || decls.len() + writes.len() >= limits.max_declarations {
                output.diagnostics.push(EnvironmentDiagnostic::LimitReached);
                break;
            }
            let node_span = span(node)?;
            if matches!(
                node.kind(),
                "func_literal"
                    | "function_literal"
                    | "arrow_function"
                    | "lambda"
                    | "lambda_expression"
                    | "closure_expression"
            ) && !ids.contains_key(&node_span)
            {
                output
                    .diagnostics
                    .push(EnvironmentDiagnostic::MissingCallableDefinition(node_span));
            }

            if ids.get(&node_span).is_some_and(|id| *id != module)
                && !is_class(node.kind())
                && let Some(name) = node.child_by_field_name("name")
                && name.kind() == "identifier"
            {
                let owner = procedure_owner(node.parent().unwrap_or(root), &ids, module);
                let (scope, field) = lexical_scope(node, language, false, &ids, root_span);
                let text = name.utf8_text(source)?.to_owned();
                decls.push(Declaration {
                    name: text.clone(),
                    scope,
                    owner,
                    at: span(name)?,
                    field,
                    class: nearest_class(node),
                });
                writes.push(Write {
                    name: text,
                    at: span(name)?,
                    rhs: node_span,
                    owner,
                    declare: true,
                    scope,
                    field,
                    class: nearest_class(node),
                });
            }
            for (target, value) in crate::operands::local_write_sources(node) {
                if target.kind() != "identifier" {
                    continue;
                }
                let at = span(target)?;
                if !seen.insert(at) {
                    continue;
                }
                let name = target.utf8_text(source)?.to_owned();
                let owner = procedure_owner(target, &ids, module);
                let variable_decl = matches!(
                    node.kind(),
                    "variable_declarator"
                        | "field_declaration"
                        | "constant_declaration"
                        | "variable_declaration"
                        | "lexical_declaration"
                        | "local_variable_declaration"
                        | "var_spec"
                        | "var_declaration"
                        | "short_var_declaration"
                        | "let_declaration"
                );
                let declare = variable_decl
                    || (language == "python" && !directives.contains_key(&(owner, name.clone())));
                let function_scoped = language == "python"
                    || (matches!(language, "javascript" | "typescript")
                        && (node.kind() == "variable_declaration"
                            || node
                                .parent()
                                .is_some_and(|n| n.kind() == "variable_declaration")));
                let (scope, field) =
                    lexical_scope(target, language, function_scoped, &ids, root_span);
                if declare {
                    decls.push(Declaration {
                        name: name.clone(),
                        scope,
                        owner,
                        at,
                        field,
                        class: nearest_class(target),
                    });
                }
                if let Some(rhs) = value {
                    writes.push(Write {
                        name,
                        at,
                        rhs: span(rhs)?,
                        owner,
                        declare,
                        scope,
                        field,
                        class: nearest_class(target),
                    });
                }
            }
            stack.extend(children(node));
        }
        // Same scope/name is one cell; assignments and var redeclarations retain alternatives.
        decls.sort_by(|a, b| {
            (a.scope.start, a.scope.end, &a.name, a.at.start).cmp(&(
                b.scope.start,
                b.scope.end,
                &b.name,
                b.at.start,
            ))
        });
        decls.dedup_by(|a, b| a.scope == b.scope && a.name == b.name);
        let mut by_name: HashMap<String, Vec<usize>> = HashMap::new();
        for (i, d) in decls.iter().enumerate() {
            by_name.entry(d.name.clone()).or_default().push(i);
        }
        let mut values = HashMap::new();
        let mut callable_spans = HashMap::new();
        for p in procedures {
            if p.id != module
                && let Some(s) = p.operands.span
            {
                callable_spans.insert(s, p.id);
            }
            for (i, e) in p.operands.expressions.iter().enumerate() {
                if let Some(s) = e.span {
                    values.entry((p.id, s)).or_insert(ExpressionId(i as u32));
                }
            }
        }
        let mut stores: HashMap<EnvironmentBinding, Vec<ValueRef>> = HashMap::new();
        let mut reads: HashMap<EnvironmentBinding, Vec<ValueRef>> = HashMap::new();
        let mut checks = 0usize;
        for p in procedures {
            for f in &p.operands.formals {
                if let Some(at) = p
                    .operands
                    .expressions
                    .get(f.value.0 as usize)
                    .and_then(|e| e.span)
                    && let Some(name) = p.operands.name(f.name)
                    && let Some(d) = by_name
                        .get(name)
                        .into_iter()
                        .flatten()
                        .map(|&i| &decls[i])
                        .find(|d| d.owner == p.id && d.at == at)
                {
                    stores
                        .entry(EnvironmentBinding {
                            owner: d.owner,
                            declaration: d.at,
                        })
                        .or_default()
                        .push(ValueRef {
                            function: p.id,
                            expression: f.value,
                        });
                }
            }
        }
        for w in writes {
            if checks >= limits.max_checks {
                break;
            }
            let d = if let Some(global) = directives.get(&(w.owner, w.name.clone())) {
                by_name
                    .get(&w.name)
                    .into_iter()
                    .flatten()
                    .map(|&i| &decls[i])
                    .filter(|d| {
                        if *global {
                            d.owner == module && !d.field
                        } else {
                            d.owner != w.owner && !d.field && contains(d.scope, w.at)
                        }
                    })
                    .min_by_key(|d| d.scope.end - d.scope.start)
            } else if w.declare {
                by_name
                    .get(&w.name)
                    .into_iter()
                    .flatten()
                    .map(|&i| &decls[i])
                    .find(|d| d.scope == w.scope && d.field == w.field && d.class == w.class)
            } else {
                resolve(
                    &w.name,
                    w.at,
                    language,
                    &decls,
                    &by_name,
                    &mut checks,
                    limits.max_checks,
                )
            };
            if let Some(d) = d
                && language == "java"
                && d.field
                && java_fields::is_static_declaration(root, d.at)
                && !values.contains_key(&(w.owner, w.rhs))
            {
                output
                    .diagnostics
                    .push(EnvironmentDiagnostic::IncompleteStorage(
                        EnvironmentBinding {
                            owner: d.owner,
                            declaration: d.at,
                        },
                    ));
            }
            if let Some(d) = d
                && (!d.field
                    || (language == "java" && java_fields::is_static_declaration(root, d.at)))
                && let Some(&value) = values.get(&(w.owner, w.rhs))
            {
                stores
                    .entry(EnvironmentBinding {
                        owner: d.owner,
                        declaration: d.at,
                    })
                    .or_default()
                    .push(ValueRef {
                        function: w.owner,
                        expression: value,
                    });
            }
        }
        for p in procedures {
            for (i, e) in p.operands.expressions.iter().enumerate() {
                if checks >= limits.max_checks {
                    break;
                }
                let value = ValueRef {
                    function: p.id,
                    expression: ExpressionId(i as u32),
                };
                let Some(at) = e.span else { continue };
                if let Some(&callee) = callable_spans.get(&at)
                    && callee != p.id
                {
                    output.callables.push(EnvironmentCallable { value, callee });
                }
                checks = checks.saturating_add(1);
                if let ExpressionKind::Member(member) = e.kind
                    && let Some(&base) = e.inputs.slice(&p.operands.inputs).and_then(|s| s.first())
                    && let Some(base_expr) = p.operands.expressions.get(base.0 as usize)
                    && let ExpressionKind::Name(name) = base_expr.kind
                    && let Some(name) = p.operands.name(name)
                    && let Some(base_at) = base_expr.span
                    && resolve(
                        name,
                        base_at,
                        language,
                        &decls,
                        &by_name,
                        &mut checks,
                        limits.max_checks,
                    )
                    .is_none()
                    && let Some(import) = program::imported(name, base_at, &imported)
                    && import.name.is_none()
                    && let Some(member) = p.operands.name(member)
                {
                    output.external_reads.push(EnvironmentExternalRead {
                        value,
                        module: import.module.clone(),
                        name: member.into(),
                    });
                }
                let ExpressionKind::Name(n) = e.kind else {
                    continue;
                };
                let Some(name) = p.operands.name(n) else {
                    continue;
                };
                if let Some(d) = resolve(
                    name,
                    at,
                    language,
                    &decls,
                    &by_name,
                    &mut checks,
                    limits.max_checks,
                ) {
                    if d.field
                        && !(language == "java" && java_fields::is_static_declaration(root, d.at))
                    {
                        let node = root
                            .named_descendant_for_byte_range(at.start as usize, at.end as usize);
                        if language == "java"
                            && node.and_then(nearest_class) == d.class
                            && let Some(receiver) = p
                                .operands
                                .formals
                                .iter()
                                .find(|f| f.kind == FormalKind::Receiver)
                        {
                            output.member_reads.push(EnvironmentMemberRead {
                                receiver: ValueRef {
                                    function: p.id,
                                    expression: receiver.value,
                                },
                                member: d.name.clone(),
                                value,
                            });
                        } else {
                            output
                                .diagnostics
                                .push(EnvironmentDiagnostic::MissingMemberReceiver(value));
                        }
                    } else {
                        reads
                            .entry(EnvironmentBinding {
                                owner: d.owner,
                                declaration: d.at,
                            })
                            .or_default()
                            .push(value);
                    }
                } else if !p
                    .operands
                    .formals
                    .iter()
                    .any(|f| p.operands.name(f.name) == Some(name))
                {
                    if let Some(import) = program::imported(name, at, &imported) {
                        if let Some(imported_name) = &import.name {
                            output.external_reads.push(EnvironmentExternalRead {
                                value,
                                module: import.module.clone(),
                                name: imported_name.clone(),
                            });
                        }
                    } else if language == "go" {
                        output.external_reads.push(EnvironmentExternalRead {
                            value,
                            module: "@package".into(),
                            name: name.into(),
                        });
                    }
                    output
                        .diagnostics
                        .push(EnvironmentDiagnostic::UnresolvedRead {
                            value,
                            name: name.into(),
                        });
                }
            }
        }
        for d in decls
            .iter()
            .filter(|d| d.owner == module && !d.field && d.scope == root_span)
        {
            let binding = EnvironmentBinding {
                owner: d.owner,
                declaration: d.at,
            };
            let mut values = stores.get(&binding).cloned().unwrap_or_default();
            values.sort_by_key(|v| (v.function, v.expression.0));
            values.dedup();
            output.exports.push(EnvironmentExport {
                name: d.name.clone(),
                binding,
                values,
            });
        }
        if language == "java" {
            java_fields::index(
                root,
                source,
                &ids,
                &decls,
                &stores,
                &values,
                limits,
                &mut output,
            )?;
        }
        if language == "java" {
            for read in &output.external_reads {
                for export in output
                    .exports
                    .iter()
                    .filter(|e| read.module == "@java" && read.name == e.name)
                {
                    for &from in &export.values {
                        if checks >= limits.max_checks {
                            break;
                        }
                        checks += 1;
                        output.transfers.push(EnvironmentTransfer {
                            binding: export.binding,
                            from,
                            to: read.value,
                        });
                    }
                }
            }
        }
        let mut ordered: Vec<_> = reads.into_iter().collect();
        ordered.sort_by_key(|(b, _)| (b.owner, b.declaration.start, b.declaration.end));
        for (binding, mut uses) in ordered {
            let mut sources = stores.remove(&binding).unwrap_or_default();
            // Ordinary local RD stays authoritative unless this cell crosses a procedure boundary.
            if !uses
                .iter()
                .chain(&sources)
                .any(|v| v.function != binding.owner)
                && !sources
                    .iter()
                    .any(|source| output.callables.iter().any(|c| c.value == *source))
            {
                continue;
            }
            uses.sort_by_key(|v| (v.function, v.expression.0));
            uses.dedup();
            sources.sort_by_key(|v| (v.function, v.expression.0));
            sources.dedup();
            if sources.is_empty() {
                output
                    .diagnostics
                    .push(EnvironmentDiagnostic::MissingProducer(binding));
            }
            for &from in &sources {
                for &to in &uses {
                    if checks >= limits.max_checks {
                        break;
                    }
                    checks += 1;
                    if from != to {
                        output
                            .transfers
                            .push(EnvironmentTransfer { binding, from, to });
                    }
                }
            }
        }
        if checks >= limits.max_checks {
            output.diagnostics.push(EnvironmentDiagnostic::LimitReached);
        }
        output
            .callables
            .sort_by_key(|c| (c.value.function, c.value.expression.0, c.callee));
        output
            .member_reads
            .sort_by_key(|r| (r.value.function, r.value.expression.0));
        Ok(output)
    }
}

#[cfg(test)]
#[path = "environment_tests.rs"]
mod tests;
