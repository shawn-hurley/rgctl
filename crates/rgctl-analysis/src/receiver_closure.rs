//! Bounded call-site refinement from complete local Java allocation producers.
//! A supplied type must be an exactly resolved named Java construction, not an
//! approximate origin seed, interface bound, factory result or visible type.
use crate::call_bindings::{CallRef, ValueRef};
use crate::cfg::ControlFlowGraph;
use crate::local_value_flow::{LocalFlowDiagnostic, LocalValueFlow};
use crate::operands::*;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use uuid::Uuid;

/// Resolver-qualified exact named Java allocation.
#[derive(Debug, Clone, Copy)]
pub struct ResolvedConstruction {
    /// Exact source-local constructed result value.
    pub value: ValueRef,
    /// Unambiguous canonical concrete class UUID from qualified extraction facts.
    pub type_id: Uuid,
}
/// All receiver producers in this supported local query resolve to these classes.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClosedReceiver {
    /// Exact invocation; aggregation across invocations remains a consumer concern.
    pub call: CallRef,
    /// Canonical possible concrete classes, retaining every reaching alternative.
    pub types: Vec<Uuid>,
    /// Exact allocation expressions supporting this result.
    pub allocations: Vec<ExpressionId>,
}
/// Qualify only Java locals whose complete native local predecessor chain ends in
/// exactly resolved named constructions. Missing/partial/formal/field/factory or
/// cyclic chains remain unqualified. This qualifies dispatch at this call site,
/// not all effects inside a target, execution success, or upgrade safety.
pub fn closed_local_receivers(
    function: Uuid,
    cfg: &ControlFlowGraph,
    flow: &LocalValueFlow,
    roots: &[ResolvedConstruction],
    max_checks: usize,
) -> Vec<ClosedReceiver> {
    if cfg.operands.language != OperandLanguage::Java
        || cfg.operands.status != OperandStatus::Captured
        || !cfg.operands.diagnostics.is_empty()
        || !cfg.operands.valid_references()
    {
        return vec![];
    }
    if flow.diagnostics.iter().any(|d| {
        matches!(
            d,
            LocalFlowDiagnostic::PartialOperands
                | LocalFlowDiagnostic::InvalidReference
                | LocalFlowDiagnostic::IncompatiblePdg
                | LocalFlowDiagnostic::LimitReached
        )
    }) {
        return vec![];
    }
    let mut bad = HashSet::new();
    for d in &flow.diagnostics {
        match d {
            LocalFlowDiagnostic::UnboundRead(v)
            | LocalFlowDiagnostic::UnmodeledWrite(v)
            | LocalFlowDiagnostic::AmbiguousOccurrence(v)
            | LocalFlowDiagnostic::IntraStatementWrites(v) => {
                bad.insert(*v);
            }
            _ => {}
        }
    }
    let mut exact: HashMap<ExpressionId, Vec<Uuid>> = HashMap::new();
    for root in roots.iter().filter(|r| r.value.function == function) {
        let Some(e) = cfg
            .operands
            .expressions
            .get(root.value.expression.0 as usize)
        else {
            continue;
        };
        if let ExpressionKind::CallResult(site) = e.kind
            && cfg
                .operands
                .calls
                .get(site.0 as usize)
                .is_some_and(|c| c.kind == InvocationKind::Construction && c.receiver.is_none())
        {
            exact
                .entry(root.value.expression)
                .or_default()
                .push(root.type_id);
        }
    }
    let mut incoming: HashMap<ExpressionId, Vec<ExpressionId>> = HashMap::new();
    for edge in &flow.transfers {
        incoming.entry(edge.to).or_default().push(edge.from);
    }
    for values in incoming.values_mut() {
        values.sort_by_key(|v| v.0);
        values.dedup();
    }
    let mut out = Vec::new();
    let mut checks = 0usize;
    for (site, call) in cfg.operands.calls.iter().enumerate() {
        let Some(receiver) = call.receiver else {
            continue;
        };
        let mut pending = vec![(receiver, false)];
        let mut active = HashSet::new();
        let mut done = HashSet::new();
        let mut types = HashSet::new();
        let mut allocations = HashSet::new();
        let mut complete = true;
        while let Some((value, exit)) = pending.pop() {
            if checks >= max_checks {
                complete = false;
                break;
            }
            checks += 1;
            if exit {
                active.remove(&value);
                done.insert(value);
                continue;
            }
            if done.contains(&value) {
                continue;
            }
            if !active.insert(value) || bad.contains(&value) {
                complete = false;
                break;
            }
            if let Some(ids) = exact.get(&value) {
                types.extend(ids.iter().copied());
                allocations.insert(value);
                active.remove(&value);
                done.insert(value);
                continue;
            }
            let Some(expression) = cfg.operands.expressions.get(value.0 as usize) else {
                complete = false;
                break;
            };
            if !matches!(
                expression.kind,
                ExpressionKind::Name(_)
                    | ExpressionKind::Parenthesized
                    | ExpressionKind::AssertedValue
                    | ExpressionKind::Conditional { .. }
            ) {
                complete = false;
                break;
            }
            let Some(inputs) = incoming.get(&value).filter(|v| !v.is_empty()) else {
                complete = false;
                break;
            };
            pending.push((value, true));
            for &input in inputs {
                pending.push((input, false));
            }
        }
        if complete && !types.is_empty() {
            let mut types: Vec<_> = types.into_iter().collect();
            types.sort();
            let mut allocations: Vec<_> = allocations.into_iter().collect();
            allocations.sort_by_key(|v| v.0);
            out.push(ClosedReceiver {
                call: CallRef {
                    caller: function,
                    site: CallSiteId(site as u32),
                },
                types,
                allocations,
            });
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg_builder::build_cfg_for_function;
    use crate::pdg::ProgramDependenceGraph;
    fn qualify(source: &str) -> (ControlFlowGraph, Vec<ClosedReceiver>) {
        let cfg = build_cfg_for_function("java", source, "exercise").unwrap();
        let pdg = ProgramDependenceGraph::build(&cfg, source.as_bytes()).unwrap();
        let flow = LocalValueFlow::build(&cfg, &pdg, Default::default());
        let function = Uuid::from_u128(1);
        let roots: Vec<_> = cfg
            .operands
            .calls
            .iter()
            .filter(|c| c.kind == InvocationKind::Construction)
            .map(|c| {
                let is_x = matches!(cfg.operands.expressions[c.callee.0 as usize].kind,
                    ExpressionKind::Name(n) if cfg.operands.name(n) == Some("X"));
                ResolvedConstruction {
                    value: ValueRef {
                        function,
                        expression: c.result,
                    },
                    type_id: Uuid::from_u128(if is_x { 100 } else { 101 }),
                }
            })
            .collect();
        let result = closed_local_receivers(function, &cfg, &flow, &roots, 10_000);
        (cfg, result)
    }
    #[test]
    fn aliases_and_reassignment_preserve_the_complete_receiver_set() {
        let (_, r) = qualify(
            "class A{static int exercise(){Y value=new W();Y alias=value;return alias.execute();}}",
        );
        assert_eq!(r.len(), 1);
        assert_eq!(r[0].types, vec![Uuid::from_u128(101)]);
        let (_, r) = qualify(
            "class A{static int exercise(){Y value=new W();value=new X();return value.execute();}}",
        );
        assert_eq!(r[0].types, vec![Uuid::from_u128(100)]);
    }
    #[test]
    fn branches_retain_both_possible_impacts() {
        let (_, r) = qualify(
            "class A{static int exercise(boolean flag){Y value=flag?new X():new W();return value.execute();}}",
        );
        assert_eq!(r.len(), 1);
        assert_eq!(r[0].types, vec![Uuid::from_u128(100), Uuid::from_u128(101)]);
    }
    #[test]
    fn parameters_fields_factories_and_anonymous_types_are_not_closed() {
        for s in [
            "class A{static int exercise(Y value){return value.execute();}}",
            "class A{Y value;int exercise(){return value.execute();}}",
            "class A{static int exercise(){Y value=make();return value.execute();}}",
            "class A{static int exercise(){Y value=new W(){public int execute(){return other();}};return value.execute();}}",
        ] {
            let (_, r) = qualify(s);
            assert!(r.is_empty(), "{s}: {r:?}");
        }
    }
    #[test]
    fn incomplete_and_budget_limited_queries_never_qualify() {
        let (_, r) = qualify(
            "class A{static int exercise(Y unknown,boolean flag){Y value=flag?new W():unknown;return value.execute();}}",
        );
        assert!(r.is_empty());
        let (cfg, r) =
            qualify("class A{static int exercise(){Y value=new W();return value.execute();}}");
        assert_eq!(r.len(), 1);
        let pdg = ProgramDependenceGraph::build(&cfg, &[]).unwrap();
        let flow = LocalValueFlow::build(&cfg, &pdg, Default::default());
        let roots: Vec<_> = cfg
            .operands
            .calls
            .iter()
            .filter(|c| c.kind == InvocationKind::Construction)
            .map(|c| ResolvedConstruction {
                value: ValueRef {
                    function: Uuid::from_u128(1),
                    expression: c.result,
                },
                type_id: Uuid::from_u128(101),
            })
            .collect();
        assert!(closed_local_receivers(Uuid::from_u128(1), &cfg, &flow, &roots, 0).is_empty());
    }
    #[test]
    fn repeated_calls_are_qualified_independently() {
        let (cfg, r) = qualify(
            "class A{static int exercise(Y unknown){Y value=new W();value.execute();return unknown.execute();}}",
        );
        assert_eq!(r.len(), 1);
        let executes: Vec<_> = cfg
            .operands
            .calls
            .iter()
            .enumerate()
            .filter(|(_, c)| {
                matches!(cfg.operands.expressions[c.callee.0 as usize].kind,
                ExpressionKind::Name(n) if cfg.operands.name(n) == Some("execute"))
            })
            .map(|(i, _)| i)
            .collect();
        assert_eq!(r[0].call.site.0 as usize, executes[0]);
    }
}
