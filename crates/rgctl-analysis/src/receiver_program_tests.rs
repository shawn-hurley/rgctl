use super::*;
use crate::cfg_builder::build_cfg_for_function;
use crate::interprocedural_cfg::InterproceduralCFG;
use crate::operands::ExpressionKind;
use rgctl_graph::{
    backend::{GraphBackend, MemoryBackend},
    schema::{Edge, EdgeType, Node, NodeType},
};
fn name(cfg: &crate::cfg::ControlFlowGraph, mut id: ExpressionId) -> Option<&str> {
    for _ in 0..32 {
        match cfg.operands.expressions.get(id.0 as usize)?.kind {
            ExpressionKind::Name(n) | ExpressionKind::Member(n) => return cfg.operands.name(n),
            ExpressionKind::TypeApplication(head) => id = head,
            _ => return None,
        }
    }
    None
}
fn analyze(
    language: &str,
    source: &str,
    names: &[&str],
    closed: &[&str],
    max_steps: usize,
) -> (InterproceduralCFG, ReceiverProgramResult) {
    let ids: HashMap<_, _> = names
        .iter()
        .enumerate()
        .map(|(i, n)| (*n, Uuid::from_u128(i as u128 + 1)))
        .collect();
    let mut cfgs = HashMap::new();
    let mut graph = MemoryBackend::new();
    for (&n, &id) in &ids {
        cfgs.insert(id, build_cfg_for_function(language, source, n).unwrap());
        let mut node = Node::new(NodeType::Function, n);
        node.id = id;
        graph.insert_node(node).unwrap();
    }
    let mut roots = Vec::new();
    let mut targets = Vec::new();
    for (&function, cfg) in &cfgs {
        for (i, c) in cfg.operands.calls.iter().enumerate() {
            if c.kind == InvocationKind::Construction {
                roots.push(ResolvedConstruction {
                    value: ValueRef {
                        function,
                        expression: c.result,
                    },
                    type_id: Uuid::from_u128(if name(cfg, c.callee) == Some("X") {
                        100
                    } else {
                        101
                    }),
                });
            } else if let Some(&callee) = name(cfg, c.callee).and_then(|n| ids.get(n)) {
                targets.push(InvocationTarget {
                    call: CallRef {
                        caller: function,
                        site: CallSiteId(i as u32),
                    },
                    callee,
                    receiver: crate::call_bindings::ReceiverSupply::None,
                });
                graph
                    .insert_edge(Edge::new(function, callee, EdgeType::Calls))
                    .unwrap();
            }
        }
        for (i, e) in cfg.operands.expressions.iter().enumerate() {
            if let ExpressionKind::Construction(head) = e.kind {
                roots.push(ResolvedConstruction {
                    value: ValueRef {
                        function,
                        expression: ExpressionId(i as u32),
                    },
                    type_id: Uuid::from_u128(if name(cfg, head) == Some("X") {
                        100
                    } else {
                        101
                    }),
                });
            }
        }
    }
    let functions: Vec<_> = ids.values().copied().collect();
    let closed_formals = closed.iter().map(|n| ids[n]).collect();
    let icfg = InterproceduralCFG::from_cfg_archive(&graph, cfgs).unwrap();
    let result = closed_program_receivers(
        &icfg,
        ReceiverProgramInputs {
            functions: &functions,
            roots: &roots,
            targets: &targets,
            closed_formals: &closed_formals,
        },
        OriginLimits {
            max_steps,
            ..Default::default()
        },
    );
    (icfg, result)
}
fn types(
    icfg: &InterproceduralCFG,
    result: &ReceiverProgramResult,
    method: &str,
) -> Vec<Vec<Uuid>> {
    result
        .receivers
        .iter()
        .filter(|r| {
            name(
                &icfg.function_cfgs[&r.call.caller],
                icfg.function_cfgs[&r.call.caller].operands.calls[r.call.site.0 as usize].callee,
            ) == Some(method)
        })
        .map(|r| r.types.clone())
        .collect()
}
#[test]
fn arguments_returns_and_generic_forwarding_are_complete_for_three_languages() {
    for (language, source, names) in [
        (
            "java",
            "class App{static int consume(Y value){return value.execute();} static <T extends Y>T forward(T value){return value;} static Y make(){return new W();} static int exercise(){consume(new W());forward(new W()).execute();return make().execute();}}",
            vec!["consume", "forward", "make", "exercise"],
        ),
        (
            "typescript",
            "function consume(value:Y){return value.execute();} function forward<T extends Y>(value:T):T{return value;} function make():Y{return new W();} function exercise(){consume(new W());forward(new W()).execute();return make().execute();}",
            vec!["consume", "forward", "make", "exercise"],
        ),
        (
            "go",
            "package sample\nfunc consume(value Y)int{return value.Execute()}\nfunc forward[T Y](value T)T{return value}\nfunc make()Y{return W{}}\nfunc exercise()int{consume(W{});forward(W{}).Execute();return make().Execute()}",
            vec!["consume", "forward", "make", "exercise"],
        ),
    ] {
        let (cfg, result) = analyze(
            language,
            source,
            &names,
            &["consume", "forward", "make"],
            100_000,
        );
        let receiver_types = types(
            &cfg,
            &result,
            if language == "go" {
                "Execute"
            } else {
                "execute"
            },
        );
        assert_eq!(receiver_types.len(), 3, "{language}: {result:?}");
        assert!(
            receiver_types
                .iter()
                .all(|v| v == &vec![Uuid::from_u128(101)]),
            "{language}: {result:?}"
        );
    }
}
#[test]
fn conditional_return_alternatives_are_all_retained() {
    for (language, source) in [
        (
            "java",
            "class App{static Y make(boolean flag){return flag?new W():new X();}static int exercise(){return make(true).execute();}}",
        ),
        (
            "typescript",
            "function make(flag:boolean):Y{return flag?new W():new X();}function exercise(){return make(true).execute();}",
        ),
        (
            "go",
            "package sample\nfunc make(flag bool)Y{if flag{return W{}};return X{}}\nfunc exercise()int{return make(true).Execute()}",
        ),
    ] {
        let (cfg, r) = analyze(language, source, &["make", "exercise"], &["make"], 100_000);
        assert_eq!(
            types(
                &cfg,
                &r,
                if language == "go" {
                    "Execute"
                } else {
                    "execute"
                }
            ),
            vec![vec![Uuid::from_u128(100), Uuid::from_u128(101)]],
            "{language}: {r:?}"
        );
        let source = source.replace("new X()", "new W()").replace("X{}", "W{}");
        let (cfg, r) = analyze(language, &source, &["make", "exercise"], &["make"], 100_000);
        assert_eq!(
            types(
                &cfg,
                &r,
                if language == "go" {
                    "Execute"
                } else {
                    "execute"
                }
            ),
            vec![vec![Uuid::from_u128(101)]],
            "{language}: {r:?}"
        );
    }
}
#[test]
fn shared_formals_merge_both_callers_and_open_formals_never_qualify() {
    let source = "class App{static int consume(Y value){return value.execute();}static int exercise(){return consume(new W());}static int other(){return consume(new X());}}";
    let (cfg, r) = analyze(
        "java",
        source,
        &["consume", "exercise", "other"],
        &["consume"],
        100_000,
    );
    assert_eq!(
        types(&cfg, &r, "execute"),
        vec![vec![Uuid::from_u128(100), Uuid::from_u128(101)]]
    );
    let (cfg, r) = analyze(
        "java",
        source,
        &["consume", "exercise", "other"],
        &[],
        100_000,
    );
    assert!(types(&cfg, &r, "execute").is_empty());
}
#[test]
fn unknown_returns_recursion_and_limits_keep_broad_dispatch() {
    for source in [
        "class App{static Y make(Y unknown,boolean flag){return flag?new W():unknown;}static int exercise(Y unknown){return make(unknown,true).execute();}}",
        "class App{static Y make(){return make();}static int exercise(){return make().execute();}}",
    ] {
        let (cfg, r) = analyze("java", source, &["make", "exercise"], &["make"], 100_000);
        assert!(types(&cfg, &r, "execute").is_empty(), "{r:?}");
    }
    let (_, r) = analyze(
        "java",
        "class App{static Y make(){return new W();}static int exercise(){return make().execute();}}",
        &["make", "exercise"],
        &["make"],
        0,
    );
    assert!(r.limited && r.receivers.is_empty());
}
