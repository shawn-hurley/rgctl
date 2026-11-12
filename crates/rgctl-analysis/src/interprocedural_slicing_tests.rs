//! Boundary regressions with complete known-call metadata. Operand-specific
//! argument binding and return transfer are tested in subsequent repair slices.

use super::*;
use crate::cfg_builder::build_cfg_for_function;
use crate::cfg_pdg_archive::{CfgPdgArchive, CfgPdgRecord};
use crate::interprocedural_cfg::InterproceduralCFG;
use rgctl_graph::schema::{Edge, EdgeType, GraphParameter, Node, NodeType};

type FunctionSpec<'a> = (&'a str, &'a str, &'a [&'a str]);

struct Fixture {
    backend: MemoryBackend,
    files: HashMap<String, String>,
    ids: HashMap<String, Uuid>,
}

impl Fixture {
    fn new(
        files: &[(&str, &str)],
        functions: &[FunctionSpec<'_>],
        calls: &[(&str, &str, usize)],
    ) -> Self {
        let mut backend = MemoryBackend::new();
        let mut ids = HashMap::new();
        for &(name, file, params) in functions {
            let node = Node::new(NodeType::Function, name)
                .with_file_path(file)
                .with_parameters(
                    params
                        .iter()
                        .map(|name| GraphParameter {
                            name: (*name).into(),
                            param_type: None,
                            default_value: None,
                        })
                        .collect(),
                );
            ids.insert(name.into(), node.id);
            backend.insert_node(node).unwrap();
        }
        for &(caller, callee, line) in calls {
            backend
                .insert_edge(
                    Edge::new(ids[caller], ids[callee], EdgeType::Calls)
                        .with_property("call_site_line".into(), line.to_string()),
                )
                .unwrap();
        }
        Self {
            backend,
            ids,
            files: files
                .iter()
                .map(|(path, source)| ((*path).into(), (*source).into()))
                .collect(),
        }
    }

    fn slice(
        &self,
        target: &str,
        variable: &str,
        line: usize,
        archived: bool,
    ) -> HashSet<(String, usize)> {
        let icfg = InterproceduralCFG::build(&self.backend, &self.files).unwrap();
        let mut archive = CfgPdgArchive::default();
        if archived {
            for (name, &id) in &self.ids {
                let node = self.backend.get_node(id).unwrap().unwrap();
                let path = node.file_path.as_deref().unwrap();
                let source = &self.files[path];
                let language =
                    crate::language_profile::language_id_from_path(std::path::Path::new(path))
                        .unwrap();
                let cfg = build_cfg_for_function(language, source, name).unwrap();
                let pdg = ProgramDependenceGraph::build(&cfg, source.as_bytes()).unwrap();
                archive.insert(CfgPdgRecord {
                    function_id: id,
                    code_hash: rgctl_graph::code_index::hash_code(source),
                    function_name: name.clone(),
                    file_path: Some(path.into()),
                    cfg: Arc::new(cfg),
                    pdg: Arc::new(pdg),
                });
            }
            // Exercise actual serialization, not just an in-memory archive view.
            archive = bincode::deserialize(&bincode::serialize(&archive).unwrap()).unwrap();
        }
        let view = archive.interprocedural_cfg_view(&self.backend).unwrap();
        let access: &dyn InterproceduralCfgAccess = if archived { &view } else { &icfg };
        let slicer = InterproceduralSlicer::new(access, &self.backend, &self.files).unwrap();
        if archived {
            slicer.preload_pdgs(&archive);
        }
        let slice = slicer
            .slice(
                self.ids[target],
                SliceCriterion {
                    variable: variable.into(),
                    line,
                },
            )
            .unwrap();
        slice
            .statements
            .iter()
            .map(|(function, node)| {
                let name = self
                    .ids
                    .iter()
                    .find(|(_, id)| *id == function)
                    .unwrap()
                    .0
                    .clone();
                (
                    name,
                    slicer.pdg_for(*function).unwrap().nodes[node]
                        .statement
                        .line,
                )
            })
            .collect()
    }
}

#[test]
fn caller_local_definitions_survive_boundary_in_six_languages() {
    for (file, source, call_line, use_line) in [
        (
            "demo.rs",
            "fn exercise() {\n let original = 41;\n let actual = original + 1;\n consume(actual);\n let unrelated = 99;\n}\nfn consume(value: i32) -> i32 {\n return value;\n}\n",
            4,
            8,
        ),
        (
            "demo.js",
            "function exercise() {\n const original = 41;\n const actual = original + 1;\n consume(actual);\n const unrelated = 99;\n}\nfunction consume(value) {\n return value;\n}\n",
            4,
            8,
        ),
        (
            "demo.ts",
            "function exercise() {\n const original = 41;\n const actual = original + 1;\n consume(actual);\n const unrelated = 99;\n}\nfunction consume(value: number) {\n return value;\n}\n",
            4,
            8,
        ),
        (
            "demo.py",
            "def exercise():\n original = 41\n actual = original + 1\n consume(actual)\n unrelated = 99\ndef consume(value):\n return value\n",
            4,
            7,
        ),
        (
            "demo.go",
            "package demo\nfunc exercise() {\n original := 41\n actual := original + 1\n consume(actual)\n unrelated := 99\n}\nfunc consume(value int) int {\n return value\n}\n",
            5,
            9,
        ),
        (
            "Demo.java",
            "class Demo {\n void exercise() {\n int original = 41;\n int actual = original + 1;\n consume(actual);\n int unrelated = 99;\n }\n int consume(int value) {\n return value;\n }\n}\n",
            5,
            9,
        ),
    ] {
        let fixture = Fixture::new(
            &[(file, source)],
            &[("exercise", file, &[]), ("consume", file, &["value"])],
            &[("exercise", "consume", call_line)],
        );
        for archived in [false, true] {
            let locations = fixture.slice("consume", "value", use_line, archived);
            for line in [call_line - 2, call_line - 1, call_line] {
                assert!(
                    locations.contains(&("exercise".into(), line)),
                    "{file}, archived={archived}: missing caller line {line}: {locations:?}"
                );
            }
            assert!(
                !locations.contains(&("exercise".into(), call_line + 1)),
                "{file}: unrelated statement entered slice"
            );
        }
    }
}

#[test]
fn renamed_alias_handoffs_follow_local_dependencies_at_every_hop() {
    let source = "fn exercise() {\n let origin = 42;\n relay(origin);\n}\nfn relay(incoming: i32) {\n let renamed = incoming;\n consume(renamed);\n}\nfn consume(value: i32) -> i32 {\n return value;\n}\n";
    let fixture = Fixture::new(
        &[("demo.rs", source)],
        &[
            ("exercise", "demo.rs", &[]),
            ("relay", "demo.rs", &["incoming"]),
            ("consume", "demo.rs", &["value"]),
        ],
        &[("exercise", "relay", 3), ("relay", "consume", 7)],
    );
    for archived in [false, true] {
        let locations = fixture.slice("consume", "value", 10, archived);
        for (name, line) in [
            ("consume", 10),
            ("relay", 6),
            ("relay", 7),
            ("exercise", 2),
            ("exercise", 3),
        ] {
            assert!(
                locations.contains(&(name.into(), line)),
                "archived={archived}: missing {name}:{line}: {locations:?}"
            );
        }
    }
}

#[test]
fn caller_predicate_dependencies_survive_the_boundary() {
    let source = "fn exercise() {\n let enabled = true;\n let actual = 42;\n if enabled {\n consume(actual);\n }\n}\nfn consume(value: i32) -> i32 {\n return value;\n}\n";
    let fixture = Fixture::new(
        &[("demo.rs", source)],
        &[
            ("exercise", "demo.rs", &[]),
            ("consume", "demo.rs", &["value"]),
        ],
        &[("exercise", "consume", 5)],
    );
    let locations = fixture.slice("consume", "value", 9, false);
    // This commit follows existing control edges. Recovering the predicate
    // variable definition in CFG lowering is a separate repair.
    for line in [3, 4, 5] {
        assert!(
            locations.contains(&("exercise".into(), line)),
            "missing caller predicate/data dependency {line}: {locations:?}"
        );
    }
}

#[test]
fn overlapping_source_lines_do_not_collide_between_functions() {
    let fixture = Fixture::new(
        &[
            (
                "caller.rs",
                "fn exercise() {\n let original = 41;\n let actual = original + 1;\n consume(actual);\n}\n",
            ),
            (
                "callee.rs",
                "fn consume(value: i32) -> i32 {\n return value;\n}\n",
            ),
        ],
        &[
            ("exercise", "caller.rs", &[]),
            ("consume", "callee.rs", &["value"]),
        ],
        &[("exercise", "consume", 4)],
    );
    let locations = fixture.slice("consume", "value", 2, false);
    for (name, line) in [
        ("consume", 2),
        ("exercise", 2),
        ("exercise", 3),
        ("exercise", 4),
    ] {
        assert!(
            locations.contains(&(name.into(), line)),
            "missing {name}:{line}: {locations:?}"
        );
    }
}

#[test]
fn recursive_boundary_worklist_reaches_a_finite_fixed_point() {
    let source = "fn exercise() {\n let original = 41;\n relay(original);\n}\nfn relay(incoming: i32) {\n let actual = incoming;\n relay(actual);\n consume(actual);\n}\nfn consume(value: i32) -> i32 {\n return value;\n}\n";
    let fixture = Fixture::new(
        &[("demo.rs", source)],
        &[
            ("exercise", "demo.rs", &[]),
            ("relay", "demo.rs", &["incoming"]),
            ("consume", "demo.rs", &["value"]),
        ],
        &[
            ("exercise", "relay", 3),
            ("relay", "relay", 7),
            ("relay", "consume", 8),
        ],
    );
    let locations = fixture.slice("consume", "value", 11, false);
    for (name, line) in [
        ("exercise", 2),
        ("exercise", 3),
        ("relay", 6),
        ("relay", 7),
        ("relay", 8),
        ("consume", 11),
    ] {
        assert!(
            locations.contains(&(name.into(), line)),
            "missing recursive dependency {name}:{line}: {locations:?}"
        );
    }
    assert_eq!(locations.len(), 6);
}
