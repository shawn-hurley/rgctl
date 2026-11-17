use super::*;
fn facts(language: &str, source: &str) -> ReceiverScopeFacts {
    let parsed = ParsedSourceFile::parse(language, source.as_bytes()).unwrap();
    receiver_scope_facts(&parsed, source.as_bytes(), language, 100_000)
}
#[test]
fn direct_declarations_and_escaped_names_are_distinguished() {
    for (language, source) in [
        (
            "java",
            "class A{static Y forward(Y value){return value;}public static Y entry(Y value){return forward(value);}void escape(){F f=A::forward;}}",
        ),
        (
            "typescript",
            "function forward(value:Y){return value;}export function entry(value:Y){return forward(value);}const escaped=forward;",
        ),
        (
            "go",
            "package sample\nfunc forward(value Y)Y{return value}\nfunc Entry(value Y)Y{return forward(value)}\nvar escaped=forward",
        ),
    ] {
        let f = facts(language, source);
        assert!(!f.private_functions.is_empty(), "{language}: {f:?}");
        assert!(f.value_names.contains("forward"), "{language}: {f:?}");
        assert!(f.direct_functions.len() >= 2);
    }
}
#[test]
fn only_simple_nominal_types_are_admitted() {
    let f = facts(
        "typescript",
        "export class W{execute(){return 200;}}class WithConstructor{constructor(){return other;}}class WithField{field=other();}class WithBase extends Unknown{}class WithStatic{static{other();}}class WithComputed{[selector](){return 1;}}",
    );
    assert_eq!(f.trivial_types.len(), 1, "{f:?}");
    let f = facts(
        "go",
        "package sample\ntype W struct{}\ntype WithField struct{field Y}\ntype Alias=Other",
    );
    assert_eq!(f.trivial_types.len(), 1, "{f:?}");
    assert!(facts("typescript", "class W{} W=Other;").dynamic_writes);
}
#[test]
fn bounded_inventory_cannot_supply_exclusion_premises() {
    let parsed = ParsedSourceFile::parse("typescript", b"class W{}").unwrap();
    assert!(receiver_scope_facts(&parsed, b"class W{}", "typescript", 0).limited);
}

#[test]
fn nominal_allocations_and_shadowed_bindings_are_explicit() {
    let f = facts("go", "package main\nfunc make()Y{return dependency.W{}} ");
    assert_eq!(f.nominal_allocations.len(), 1);
    assert_eq!(f.nominal_allocations[0].type_name, "dependency.W");
    let f = facts(
        "typescript",
        "import {W} from './dep'; function exercise(){const W=Other;return new W();}",
    );
    assert!(f.shadowed_names.contains("W"));
    let f = facts("typescript", "class W{get execute(){return callback;}}");
    assert!(f.trivial_types.is_empty());
}

#[test]
fn pattern_and_catch_bindings_cannot_shadow_a_constructor_silently() {
    for source in [
        "import {W} from './dep'; function exercise(){const {W}=other;return new W();}",
        "import {W} from './dep'; function exercise(W:any){return new W();}",
        "import {W} from './dep'; function exercise(){try{other();}catch(W){return new W();}}",
    ] {
        let f = facts("typescript", source);
        assert!(f.shadowed_names.contains("W"), "{source}: {f:?}");
    }
}
