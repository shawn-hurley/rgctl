use super::*;
use crate::call_bindings::{CallRef, InvocationTarget, ReceiverSupply};
use crate::cfg::ControlFlowGraph;
use crate::interprocedural_cfg::InterproceduralCFG;
use crate::value_origins::*;
use rgctl_graph::backend::{GraphBackend, MemoryBackend};
use rgctl_graph::schema::{Node, NodeType};

struct Fixture {
    cfgs: HashMap<Uuid, ControlFlowGraph>,
    ids: HashMap<String, Uuid>,
    facts: EnvironmentFacts,
}
impl Fixture {
    fn new(language: &str, source: &str, names: &[&str]) -> Self {
        Self::new_with_base(language, source, names, 1)
    }
    fn new_with_base(language: &str, source: &str, names: &[&str], base: u128) -> Self {
        let parsed = ParsedSourceFile::parse(language, source.as_bytes()).unwrap();
        let module = Uuid::from_u128(base);
        let mut cfgs = HashMap::new();
        cfgs.insert(
            module,
            parsed
                .build_module_cfg(language, source.as_bytes())
                .unwrap(),
        );
        let mut ids = HashMap::new();
        for (i, &name) in names.iter().enumerate() {
            let id = Uuid::from_u128(base + i as u128 + 1);
            ids.insert(name.into(), id);
            cfgs.insert(
                id,
                parsed.build_cfg(language, source.as_bytes(), name).unwrap(),
            );
        }
        let mut procedures: Vec<_> = cfgs
            .iter()
            .map(|(&id, cfg)| EnvironmentProcedure {
                id,
                operands: &cfg.operands,
            })
            .collect();
        procedures.sort_by_key(|p| p.id);
        let facts = parsed
            .environment_facts(
                language,
                source.as_bytes(),
                module,
                &procedures,
                Default::default(),
            )
            .unwrap();
        Self { cfgs, ids, facts }
    }
    fn solve(&self) -> OriginAnalysis {
        let mut backend = MemoryBackend::new();
        for &id in self.cfgs.keys() {
            let mut n = Node::new(NodeType::Function, "fixture");
            n.id = id;
            backend.insert_node(n).unwrap();
        }
        let mut seeds = Vec::new();
        let mut targets = Vec::new();
        let mut members = Vec::new();
        for (&function, cfg) in &self.cfgs {
            for (i, c) in cfg.operands.calls.iter().enumerate() {
                let label = match cfg.operands.expressions[c.callee.0 as usize].kind {
                    ExpressionKind::Name(n) | ExpressionKind::Member(n) => cfg.operands.name(n),
                    _ => None,
                };
                if let Some(ty) = match label {
                    Some("X") => Some(100),
                    Some("W") => Some(101),
                    Some("Box") => Some(102),
                    _ => None,
                } {
                    seeds.push(OriginSeed {
                        value: ValueRef {
                            function,
                            expression: c.result,
                        },
                        type_id: Some(Uuid::from_u128(ty)),
                    });
                }
                if let Some(&callee) = label.and_then(|n| self.ids.get(n)) {
                    let target = InvocationTarget {
                        call: CallRef {
                            caller: function,
                            site: CallSiteId(i as u32),
                        },
                        callee,
                        receiver: if c.kind == InvocationKind::Construction {
                            ReceiverSupply::Constructed
                        } else if c.receiver.is_some() {
                            ReceiverSupply::Member
                        } else {
                            ReceiverSupply::None
                        },
                    };
                    if matches!(label, Some("execute" | "Execute")) {
                        members.push(MemberCandidate {
                            target,
                            receiver_type: Uuid::from_u128(100),
                        });
                    } else {
                        targets.push(target);
                    }
                }
            }
            for (i, e) in cfg.operands.expressions.iter().enumerate() {
                if let ExpressionKind::Construction(head) = e.kind
                    && let ExpressionKind::Name(n) = cfg.operands.expressions[head.0 as usize].kind
                    && let Some(ty) = match cfg.operands.name(n) {
                        Some("X") => Some(100),
                        Some("W") => Some(101),
                        _ => None,
                    }
                {
                    seeds.push(OriginSeed {
                        value: ValueRef {
                            function,
                            expression: ExpressionId(i as u32),
                        },
                        type_id: Some(Uuid::from_u128(ty)),
                    });
                }
            }
        }
        seeds.sort_by_key(|s| (s.value.function, s.value.expression.0, s.type_id));
        targets.sort_by_key(|t| (t.call.caller, t.call.site.0, t.callee));
        members.sort_by_key(|m| (m.target.call.caller, m.target.call.site.0));
        let callables: Vec<_> = self
            .facts
            .callables
            .iter()
            .map(|c| CallableCandidate {
                value: c.value,
                callee: c.callee,
                receiver: ReceiverSupply::None,
                requirement: None,
            })
            .collect();
        let icfg = InterproceduralCFG::from_cfg_archive(&backend, self.cfgs.clone()).unwrap();
        OriginAnalysis::build_with_environment(
            &icfg,
            OriginInputs {
                seeds: &seeds,
                targets: &targets,
                members: &members,
                callables: &callables,
                ..Default::default()
            },
            &self.facts,
            Default::default(),
        )
    }
    fn reaches_x(&self) -> bool {
        let output = self.solve();
        let execute = self
            .ids
            .get("execute")
            .or_else(|| self.ids.get("Execute"))
            .unwrap();
        output
            .receiver_targets
            .iter()
            .any(|r| r.target.callee == *execute)
            || output
                .callable_targets
                .iter()
                .any(|r| r.target.callee == *execute)
    }
}
#[test]
fn module_state_supplies_body_reads_in_four_languages() {
    for (language, source, names) in [
        (
            "javascript",
            "const selected=new X();function exercise(){return selected.execute();}class X{execute(){return 100;}}",
            vec!["exercise", "execute"],
        ),
        (
            "typescript",
            "const selected:Y=new X();function exercise(){return selected.execute();}class X{execute(){return 100;}}",
            vec!["exercise", "execute"],
        ),
        (
            "python",
            "selected=X()\ndef exercise():\n return selected.execute()\nclass X:\n def execute(self):\n  return 100\n",
            vec!["exercise", "execute"],
        ),
        (
            "go",
            "package demo\nvar selected Y=X{}\nfunc exercise()int{return selected.Execute()}\nfunc(x X)Execute()int{return 100}",
            vec!["exercise", "Execute"],
        ),
    ] {
        let f = Fixture::new(language, source, &names);
        assert!(!f.facts.transfers.is_empty(), "{language}");
        assert!(f.reaches_x(), "{language}: {:?}", f.solve());
    }
}
#[test]
fn enclosing_bindings_supply_native_capture_flow_without_fallback() {
    let f = Fixture::new(
        "python",
        "def exercise():\n selected=X()\n def nested():\n  return selected.execute()\n return nested()\nclass X:\n def execute(self):\n  return 100\n",
        &["exercise", "nested", "execute"],
    );
    let out = f.solve();
    assert!(f.reaches_x(), "{out:?}");
    assert!(
        out.transfers
            .iter()
            .any(|e| matches!(e.cause, OriginTransferCause::Environment { .. }))
    );
}
#[test]
fn captured_cells_retain_writes_after_creation_and_nonlocal_updates() {
    for source in [
        "def exercise():\n selected=W()\n def nested():\n  return selected.execute()\n selected=X()\n return nested()\nclass X:\n def execute(self):\n  return 100\n",
        "def exercise():\n selected=W()\n def nested():\n  nonlocal selected\n  selected=X()\n nested()\n return selected.execute()\nclass X:\n def execute(self):\n  return 100\n",
    ] {
        let f = Fixture::new("python", source, &["exercise", "nested", "execute"]);
        assert!(f.reaches_x(), "{:?}", f.solve());
    }
}
#[test]
fn an_inner_declaration_shadows_an_outer_cell_with_the_same_name() {
    let f = Fixture::new(
        "python",
        "def exercise():\n selected=X()\n def nested():\n  selected=W()\n  return selected.execute()\n return nested()\nclass X:\n def execute(self):\n  return 100\n",
        &["exercise", "nested", "execute"],
    );
    assert!(!f.reaches_x(), "{:?}", f.solve());
}
#[test]
fn module_and_function_shadowing_do_not_join_by_name() {
    let f = Fixture::new(
        "javascript",
        "const selected=new X();function exercise(){const selected=new W();return selected.execute();}class X{execute(){return 100;}}",
        &["exercise", "execute"],
    );
    assert!(!f.reaches_x(), "{:?}", f.solve());
}
#[test]
fn java_member_roles_and_implicit_field_lookup_share_object_state() {
    for read in ["value", "this.value"] {
        let source = format!(
            "class App{{static class Box{{X value;Box(X value){{this.value=value;}}int run(){{return {read}.execute();}}}}static int exercise(){{return new Box(new X()).run();}}}}class X{{int execute(){{return 100;}}}}"
        );
        let f = Fixture::new("java", &source, &["Box", "run", "exercise", "execute"]);
        assert_eq!(f.cfgs[&f.ids["Box"]].operands.field_writes.len(), 1);
        assert!(f.reaches_x(), "{read}: {:?}", f.solve());
    }
}
#[test]
fn module_cfg_does_not_execute_declared_function_bodies() {
    let f = Fixture::new(
        "javascript",
        "function never(){throw new Error();}const selected=new X();function exercise(){return selected.execute();}class X{execute(){return 100;}}",
        &["never", "exercise", "execute"],
    );
    let module = &f.cfgs[&Uuid::from_u128(1)];
    assert!(
        module
            .blocks
            .values()
            .flat_map(|b| &b.statements)
            .all(|s| !s.text.contains("throw"))
    );
    assert!(f.reaches_x());
}
#[test]
fn indexing_limits_are_explicit_partial_coverage() {
    let source = "const selected=new X();function exercise(){return selected.execute();}";
    let parsed = ParsedSourceFile::parse("javascript", source.as_bytes()).unwrap();
    let cfg = parsed
        .build_module_cfg("javascript", source.as_bytes())
        .unwrap();
    let module = Uuid::from_u128(1);
    let facts = parsed
        .environment_facts(
            "javascript",
            source.as_bytes(),
            module,
            &[EnvironmentProcedure {
                id: module,
                operands: &cfg.operands,
            }],
            EnvironmentLimits {
                max_nodes: 0,
                ..Default::default()
            },
        )
        .unwrap();
    assert!(
        facts
            .diagnostics
            .iter()
            .any(|d| matches!(d, EnvironmentDiagnostic::LimitReached))
    );
}

#[test]
fn escaped_closures_retain_their_enclosing_binding() {
    for (language, source) in [
        (
            "python",
            "def make():\n selected=X()\n def nested():\n  return selected.execute()\n return nested\ndef exercise():\n return make()()\nclass X:\n def execute(self):\n  return 100\n",
        ),
        (
            "javascript",
            "function make(){let selected=new X();function nested(){return selected.execute();}return nested;}function exercise(){return make()();}class X{execute(){return 100;}}",
        ),
    ] {
        let f = Fixture::new(language, source, &["make", "nested", "exercise", "execute"]);
        let out = f.solve();
        assert!(f.reaches_x(), "{language}: {out:?}");
        assert!(
            out.callable_targets
                .iter()
                .any(|r| r.target.callee == f.ids["nested"]
                    && r.target.call.caller == f.ids["exercise"]),
            "{out:?}"
        );
    }
}

#[test]
fn imported_module_state_uses_the_owning_source_file() {
    for (language, state, app, path_a, path_b) in [
        (
            "javascript",
            "const selected=new X();class X{execute(){return 100;}}",
            "import {selected as chosen} from './state.js';function exercise(){return chosen.execute();}",
            "application/state.js",
            "application/app.js",
        ),
        (
            "typescript",
            "const selected:Y=new X();class X{execute(){return 100;}}",
            "import * as state from './state';function exercise(){return state.selected.execute();}",
            "application/state.ts",
            "application/app.ts",
        ),
        (
            "python",
            "selected=X()\nclass X:\n def execute(self):\n  return 100\n",
            "from .state import selected as chosen\ndef exercise():\n return chosen.execute()\n",
            "application/state.py",
            "application/app.py",
        ),
        (
            "go",
            "package main\nvar selected Y=X{}\nfunc(x X)Execute()int{return 100}",
            "package main\nfunc exercise()int{return selected.Execute()}",
            "application/state.go",
            "application/main.go",
        ),
    ] {
        let method = if language == "go" {
            "Execute"
        } else {
            "execute"
        };
        let mut a = Fixture::new_with_base(language, state, &[method], 10);
        let b = Fixture::new_with_base(language, app, &["exercise"], 20);
        let facts = link_environment_modules(
            vec![
                EnvironmentModule {
                    path: path_a.into(),
                    language: language.into(),
                    facts: a.facts,
                },
                EnvironmentModule {
                    path: path_b.into(),
                    language: language.into(),
                    facts: b.facts,
                },
            ],
            250_000,
        );
        a.cfgs.extend(b.cfgs);
        a.ids.extend(b.ids);
        a.facts = facts;
        assert!(a.reaches_x(), "{language}: {:?}", a.solve());
    }
}

#[test]
fn unrelated_modules_with_the_same_export_name_do_not_share_state() {
    let mut a = Fixture::new_with_base(
        "javascript",
        "const selected=new X();class X{execute(){return 100;}}",
        &["execute"],
        10,
    );
    let b = Fixture::new_with_base("javascript", "const selected=new W();", &[], 20);
    let c = Fixture::new_with_base(
        "javascript",
        "import {selected} from './other.js';function exercise(){return selected.execute();}",
        &["exercise"],
        30,
    );
    let facts = link_environment_modules(
        vec![
            EnvironmentModule {
                path: "application/state.js".into(),
                language: "javascript".into(),
                facts: a.facts,
            },
            EnvironmentModule {
                path: "application/other.js".into(),
                language: "javascript".into(),
                facts: b.facts,
            },
            EnvironmentModule {
                path: "application/app.js".into(),
                language: "javascript".into(),
                facts: c.facts,
            },
        ],
        250_000,
    );
    a.cfgs.extend(b.cfgs);
    a.cfgs.extend(c.cfgs);
    a.ids.extend(c.ids);
    a.facts = facts;
    assert!(!a.reaches_x(), "{:?}", a.solve());
}

#[test]
fn generic_type_arguments_do_not_replace_the_constructor_head() {
    let f = Fixture::new(
        "java",
        "class App{static Object exercise(){return new Box<Y>();}}",
        &["exercise"],
    );
    let id = f.ids["exercise"];
    let cfg = &f.cfgs[&id];
    let (app, head) = cfg
        .operands
        .expressions
        .iter()
        .enumerate()
        .find_map(|(i, e)| {
            if let ExpressionKind::TypeApplication(head) = e.kind {
                Some((ExpressionId(i as u32), head))
            } else {
                None
            }
        })
        .unwrap();
    let mut backend = MemoryBackend::new();
    let mut node = Node::new(NodeType::Function, "exercise");
    node.id = id;
    backend.insert_node(node).unwrap();
    let icfg =
        InterproceduralCFG::from_cfg_archive(&backend, HashMap::from([(id, cfg.clone())])).unwrap();
    let ctor = ConstructorCandidate {
        value: ValueRef {
            function: id,
            expression: head,
        },
        type_id: Uuid::from_u128(102),
        callee: None,
    };
    let out =
        OriginAnalysis::build_with_values(&icfg, &[], &[], &[], &[], &[ctor], Default::default());
    assert!(
        out.origins(ValueRef {
            function: id,
            expression: app
        })
        .iter()
        .any(|o| out.seeds[o.0 as usize].type_id.is_none())
    );
    assert!(
        out.construction_evidence
            .iter()
            .any(|e| e.type_id == Uuid::from_u128(102))
    );
}
