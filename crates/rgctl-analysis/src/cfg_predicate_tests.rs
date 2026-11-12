//! Native predicate lowering must retain scoped def/use facts for the PDG.

use super::*;
use crate::pdg::ProgramDependenceGraph;
use crate::slicing::{BackwardSlicer, SliceCriterion};

#[test]
fn predicate_uses_reach_their_definitions_in_six_languages() {
    for (language, source, definition_line) in [
        (
            "rust",
            "fn example() {\n let enabled = true;\n if enabled { consume(); }\n}\n",
            2,
        ),
        (
            "javascript",
            "function example() {\n const enabled = true;\n if (enabled) { consume(); }\n}\n",
            2,
        ),
        (
            "typescript",
            "function example() {\n const enabled: boolean = true;\n if (enabled) { consume(); }\n}\n",
            2,
        ),
        (
            "python",
            "def example():\n enabled = True\n if enabled:\n  consume()\n",
            2,
        ),
        (
            "go",
            "package demo\nfunc example() {\n enabled := true\n if enabled { consume() }\n}\n",
            3,
        ),
        (
            "java",
            "class Demo {\n void example() {\n boolean enabled = true;\n if (enabled) { consume(); }\n }\n}\n",
            3,
        ),
    ] {
        let cfg = build_cfg_for_function(language, source, "example").unwrap();
        let pdg = ProgramDependenceGraph::build(&cfg, source.as_bytes()).unwrap();
        let predicate = pdg
            .nodes
            .values()
            .find(|n| n.statement.kind == StatementKind::Branch && n.statement.text == "enabled")
            .unwrap();
        assert!(
            predicate.used_vars.contains("enabled"),
            "{language}: predicate discarded its input"
        );
        assert!(
            pdg.data_deps.iter().any(|d| d.to == predicate.id
                && d.variable == "enabled"
                && pdg.nodes[&d.from].statement.line == definition_line),
            "{language}: missing definition → predicate edge"
        );
        let slice = BackwardSlicer::new(&pdg, &cfg)
            .slice(SliceCriterion {
                variable: "enabled".into(),
                line: predicate.statement.line,
            })
            .unwrap();
        assert!(
            slice.lines.contains(&definition_line),
            "{language}: predicate slice omitted its definition"
        );
    }
}

#[test]
fn short_circuit_operands_keep_separate_def_use_facts() {
    let source = "fn example() {\n let left = true;\n let right = true;\n if left && right { consume(); }\n}\n";
    let cfg = build_cfg_for_function("rust", source, "example").unwrap();
    let pdg = ProgramDependenceGraph::build(&cfg, source.as_bytes()).unwrap();
    for (name, definition_line) in [("left", 2), ("right", 3)] {
        let predicate = pdg
            .nodes
            .values()
            .find(|n| n.statement.kind == StatementKind::Branch && n.statement.text == name)
            .unwrap();
        assert_eq!(predicate.used_vars, HashSet::from([name.to_string()]));
        assert!(pdg.data_deps.iter().any(|d| d.to == predicate.id
            && d.variable == name
            && pdg.nodes[&d.from].statement.line == definition_line));
    }
}

#[test]
fn shadowed_predicate_uses_the_inner_scoped_definition() {
    let source = "fn example() {\n let enabled = false;\n {\n let enabled = true;\n if enabled { consume(); }\n }\n}\n";
    let cfg = build_cfg_for_function("rust", source, "example").unwrap();
    let pdg = ProgramDependenceGraph::build(&cfg, source.as_bytes()).unwrap();
    let predicate = pdg
        .nodes
        .values()
        .find(|n| n.statement.kind == StatementKind::Branch && n.statement.text == "enabled")
        .unwrap();
    assert!(
        predicate
            .used_vars
            .iter()
            .any(|v| v.starts_with("enabled#")),
        "predicate did not resolve lexical shadowing: {:?}",
        predicate.used_vars
    );
    let definitions: Vec<_> = pdg
        .data_deps
        .iter()
        .filter(|d| d.to == predicate.id && d.variable.starts_with("enabled"))
        .map(|d| pdg.nodes[&d.from].statement.line)
        .collect();
    assert_eq!(definitions, [4]);
}

#[test]
fn assignment_predicate_keeps_its_definition_and_rhs_use() {
    let source = "void example() {\n int enabled = 0;\n int next = 1;\n if ((enabled = next)) { consume(enabled); }\n}\n";
    let cfg = build_cfg_for_function("c", source, "example").unwrap();
    let predicate = cfg
        .blocks
        .values()
        .flat_map(|b| &b.statements)
        .find(|s| s.kind == StatementKind::Branch)
        .unwrap();
    assert!(
        predicate
            .defined_vars
            .iter()
            .any(|v| v.defines_name("enabled"))
    );
    assert!(predicate.used_vars.iter().any(|v| v == "next"));
}
