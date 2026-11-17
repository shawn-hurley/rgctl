//! Complete producer checks across resolver-selected direct invocation bindings.
//! This is a query projection, not a change to the merged possible-origin graph.
use crate::call_bindings::{
    BindingSource, CallBindings, CallRef, InvocationTarget, TransferKind, ValueRef,
};
use crate::interprocedural_cfg::InterproceduralCfgAccess;
use crate::local_value_flow::{LocalFlowDiagnostic, LocalValueFlow};
use crate::operands::*;
use crate::pdg::ProgramDependenceGraph;
use crate::receiver_closure::ResolvedConstruction;
use crate::value_origins::OriginLimits;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use uuid::Uuid;

/// Explicit resolver premises; none are inferred from a nonempty origin set.
pub struct ReceiverProgramInputs<'a> {
    /// Complete bounded procedure inventory for this projection.
    pub functions: &'a [Uuid],
    /// Exact nominal allocations admitted by the consumer's language/type guards.
    pub roots: &'a [ResolvedConstruction],
    /// Complete possible targets of each admitted direct source invocation.
    pub targets: &'a [InvocationTarget],
    /// Internal, unescaped procedures whose entire incoming invocation inventory
    /// is represented by `targets`. Unknown/external entries must not be included.
    pub closed_formals: &'a HashSet<Uuid>,
}
/// Receiver producers accounted for across the selected direct bindings.
#[derive(Debug, Serialize, Deserialize)]
pub struct ProgramClosedReceiver {
    /// Exact source invocation.
    pub call: CallRef,
    /// All reaching canonical concrete types, including alternative callers.
    pub types: Vec<Uuid>,
    /// Function-qualified allocation evidence; factory roots live in callees.
    pub allocations: Vec<ValueRef>,
}
/// Coverage evidence for a bounded complete-producer query.
#[derive(Debug, Serialize, Deserialize)]
pub struct ReceiverProgramResult {
    /// Qualified receivers only; missing entries retain conservative candidates.
    pub receivers: Vec<ProgramClosedReceiver>,
    /// Functions whose syntax or local flow was partial.
    pub incomplete_functions: Vec<Uuid>,
    /// Invalid or partially bound direct invocations.
    pub incomplete_calls: Vec<CallRef>,
    /// Global budget exhausted. No exclusions are returned in that case.
    pub limited: bool,
}
struct State {
    incoming: HashMap<ValueRef, Vec<ValueRef>>,
    exact: HashMap<ValueRef, Vec<Uuid>>,
    bad: HashSet<ValueRef>,
    bad_functions: HashSet<Uuid>,
    returns: HashSet<ValueRef>,
    closed_formals: HashSet<Uuid>,
}
impl State {
    fn producers<C: InterproceduralCfgAccess + ?Sized>(
        &self,
        icfg: &C,
        receiver: ValueRef,
        remaining: &mut usize,
    ) -> Option<(Vec<Uuid>, Vec<ValueRef>)> {
        let mut pending = vec![(receiver, false)];
        let mut active = HashSet::new();
        let mut done = HashSet::new();
        let mut types = HashSet::new();
        let mut allocations = HashSet::new();
        while let Some((value, exit)) = pending.pop() {
            *remaining = remaining.checked_sub(1)?;
            if exit {
                active.remove(&value);
                done.insert(value);
                continue;
            }
            if done.contains(&value) {
                continue;
            }
            if self.bad_functions.contains(&value.function)
                || self.bad.contains(&value)
                || !active.insert(value)
            {
                return None;
            }
            if let Some(ids) = self.exact.get(&value) {
                types.extend(ids.iter().copied());
                allocations.insert(value);
                active.remove(&value);
                done.insert(value);
                continue;
            }
            let cfg = icfg.get_cfg(value.function)?;
            let e = cfg.operands.expressions.get(value.expression.0 as usize)?;
            let supported = match e.kind {
                ExpressionKind::Name(_)
                | ExpressionKind::Parenthesized
                | ExpressionKind::AssertedValue
                | ExpressionKind::Conditional { .. } => true,
                ExpressionKind::Formal(_) => self.closed_formals.contains(&value.function),
                ExpressionKind::CallResult(_) => self.returns.contains(&value),
                _ => false,
            };
            if !supported {
                return None;
            }
            let predecessors = self.incoming.get(&value).filter(|v| !v.is_empty())?;
            pending.push((value, true));
            pending.extend(predecessors.iter().map(|&v| (v, false)));
        }
        if types.is_empty() {
            return None;
        }
        let mut types: Vec<_> = types.into_iter().collect();
        types.sort();
        let mut allocations: Vec<_> = allocations.into_iter().collect();
        allocations.sort_by_key(|v| (v.function, v.expression.0));
        Some((types, allocations))
    }
}
/// Follow all modeled local, actual/formal and return/result producers. Formal
/// origins deliberately merge every admitted caller: this cannot exclude one
/// caller's X from another caller's W. Unknown roots, recursive cycles, partial
/// mappings, storage and non-scalar transfer conventions remain unqualified.
pub fn closed_program_receivers<C: InterproceduralCfgAccess + ?Sized>(
    icfg: &C,
    inputs: ReceiverProgramInputs<'_>,
    limits: OriginLimits,
) -> ReceiverProgramResult {
    let mut out = ReceiverProgramResult {
        receivers: vec![],
        incomplete_functions: vec![],
        incomplete_calls: vec![],
        limited: false,
    };
    if inputs.functions.len() > limits.max_functions
        || inputs.targets.len() > limits.max_targets
        || inputs.roots.len() > limits.max_facts
    {
        out.limited = true;
        return out;
    }
    let mut state = State {
        incoming: HashMap::new(),
        exact: HashMap::new(),
        bad: HashSet::new(),
        bad_functions: HashSet::new(),
        returns: HashSet::new(),
        closed_formals: inputs.closed_formals.clone(),
    };
    let mut functions = inputs.functions.to_vec();
    functions.sort();
    functions.dedup();
    let mut transfers = 0usize;
    for &function in &functions {
        let Some(cfg) = icfg.get_cfg(function) else {
            state.bad_functions.insert(function);
            continue;
        };
        if !matches!(
            cfg.operands.language,
            OperandLanguage::Java | OperandLanguage::TypeScript | OperandLanguage::Go
        ) || cfg.operands.status != OperandStatus::Captured
            || !cfg.operands.diagnostics.is_empty()
            || !cfg.operands.valid_references()
        {
            state.bad_functions.insert(function);
            continue;
        }
        let Ok(pdg) = ProgramDependenceGraph::build(cfg, &[]) else {
            state.bad_functions.insert(function);
            continue;
        };
        let flow = LocalValueFlow::build(cfg, &pdg, limits.local);
        for diagnostic in &flow.diagnostics {
            match diagnostic {
                LocalFlowDiagnostic::UnboundRead(v)
                | LocalFlowDiagnostic::UnmodeledWrite(v)
                | LocalFlowDiagnostic::AmbiguousOccurrence(v)
                | LocalFlowDiagnostic::IntraStatementWrites(v) => {
                    state.bad.insert(ValueRef {
                        function,
                        expression: *v,
                    });
                }
                _ => {
                    state.bad_functions.insert(function);
                }
            }
        }
        for edge in flow.transfers {
            transfers += 1;
            if transfers > limits.max_transfers {
                out.limited = true;
                return out;
            }
            state
                .incoming
                .entry(ValueRef {
                    function,
                    expression: edge.to,
                })
                .or_default()
                .push(ValueRef {
                    function,
                    expression: edge.from,
                });
        }
    }
    for root in inputs.roots {
        if functions.binary_search(&root.value.function).is_err() {
            continue;
        }
        let Some(cfg) = icfg.get_cfg(root.value.function) else {
            continue;
        };
        let Some(e) = cfg
            .operands
            .expressions
            .get(root.value.expression.0 as usize)
        else {
            continue;
        };
        let nominal = match e.kind {
            ExpressionKind::CallResult(site) => cfg
                .operands
                .calls
                .get(site.0 as usize)
                .is_some_and(|c| c.kind == InvocationKind::Construction && c.receiver.is_none()),
            ExpressionKind::Construction(_) => cfg.operands.language == OperandLanguage::Go,
            _ => false,
        };
        if nominal {
            state
                .exact
                .entry(root.value)
                .or_default()
                .push(root.type_id);
        }
    }
    let mut bindings = CallBindings::new(icfg);
    let mut targets = inputs.targets.to_vec();
    targets.sort_by_key(|t| (t.call.caller, t.call.site.0, t.callee));
    targets.dedup();
    for target in targets {
        let result = bindings.bind(target);
        let complete = functions.binary_search(&target.call.caller).is_ok()
            && functions.binary_search(&target.callee).is_ok()
            && result.as_ref().is_ok_and(|b| b.diagnostics.len == 0);
        if !complete {
            out.incomplete_calls.push(target.call);
            state.closed_formals.remove(&target.callee);
            if let Some(call) = icfg
                .get_cfg(target.call.caller)
                .and_then(|c| c.operands.calls.get(target.call.site.0 as usize))
            {
                state.bad.insert(ValueRef {
                    function: target.call.caller,
                    expression: call.result,
                });
            }
            continue;
        }
        let Ok(binding) = result else {
            continue;
        };
        for transfer in binding.transfers.slice(bindings.transfers()).unwrap_or(&[]) {
            let scalar = matches!(
                transfer.kind,
                TransferKind::ActualToFormal
                    | TransferKind::ReceiverToFormal
                    | TransferKind::ReturnToResult { position: 0 }
            );
            if let BindingSource::Expression(from) = transfer.from
                && scalar
            {
                transfers += 1;
                if transfers > limits.max_transfers {
                    out.limited = true;
                    return out;
                }
                state.incoming.entry(transfer.to).or_default().push(from);
                if matches!(transfer.kind, TransferKind::ReturnToResult { position: 0 }) {
                    state.returns.insert(transfer.to);
                }
            } else {
                state.bad.insert(transfer.to);
            }
        }
    }
    for incoming in state.incoming.values_mut() {
        incoming.sort_by_key(|v| (v.function, v.expression.0));
        incoming.dedup();
    }
    if state.incoming.len() + state.bad.len() + state.exact.len() > limits.max_facts {
        out.limited = true;
        return out;
    }
    let mut remaining = limits.max_steps;
    for &caller in &functions {
        let Some(cfg) = icfg.get_cfg(caller) else {
            continue;
        };
        for (site, call) in cfg.operands.calls.iter().enumerate() {
            if let Some(receiver) = call.receiver
                && let Some((types, allocations)) = state.producers(
                    icfg,
                    ValueRef {
                        function: caller,
                        expression: receiver,
                    },
                    &mut remaining,
                )
            {
                out.receivers.push(ProgramClosedReceiver {
                    call: CallRef {
                        caller,
                        site: CallSiteId(site as u32),
                    },
                    types,
                    allocations,
                });
            }
            if remaining == 0 {
                out.receivers.clear();
                out.limited = true;
                return out;
            }
        }
    }
    out.incomplete_functions = state.bad_functions.into_iter().collect();
    out.incomplete_functions.sort();
    out.incomplete_calls.sort_by_key(|c| (c.caller, c.site.0));
    out.incomplete_calls.dedup();
    out
}

#[cfg(test)]
#[path = "receiver_program_tests.rs"]
mod tests;
