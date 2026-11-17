//! Shared native Java initialization identities and source-order selection.
use tree_sitter::Node;

/// Whether a declaration has the Java `static` modifier (interface fields are implicit).
pub fn is_static(node: Node<'_>) -> bool {
    if node.kind() == "constant_declaration" || node.kind() == "static_initializer" {
        return true;
    }
    let mut c = node.walk();
    node.named_children(&mut c)
        .filter(|n| n.kind() == "modifiers")
        .any(|n| {
            let mut c = n.walk();
            n.children(&mut c).any(|n| n.kind() == "static")
        })
}
/// Direct initializer statements/declarations, in Java source order. Nested types
/// and callable bodies are intentionally excluded from the enclosing initializer.
pub fn initialization_roots(owner: Node<'_>, static_: bool) -> Vec<Node<'_>> {
    let body = if matches!(owner.kind(), "class_body" | "interface_body" | "enum_body") {
        Some(owner)
    } else {
        owner.child_by_field_name("body")
    };
    let Some(body) = body else { return Vec::new() };
    let mut cursor = body.walk();
    let mut result = Vec::new();
    for node in body.named_children(&mut cursor) {
        if node.kind() == "enum_body_declarations" {
            result.extend(initialization_roots_in_declarations(node, static_));
        } else {
            select_root(node, static_, &mut result);
        }
    }
    result
}
fn initialization_roots_in_declarations(node: Node<'_>, static_: bool) -> Vec<Node<'_>> {
    let mut result = Vec::new();
    let mut c = node.walk();
    for child in node.named_children(&mut c) {
        select_root(child, static_, &mut result);
    }
    result
}
fn select_root<'a>(node: Node<'a>, static_: bool, result: &mut Vec<Node<'a>>) {
    match node.kind() {
        "field_declaration" | "constant_declaration" if is_static(node) == static_ => {
            let mut c = node.walk();
            if node.named_children(&mut c).any(|n| {
                n.kind() == "variable_declarator" && n.child_by_field_name("value").is_some()
            }) {
                result.push(node);
            }
        }
        "static_initializer" if static_ => {
            let mut c = node.walk();
            if let Some(block) = node.named_children(&mut c).find(|n| n.kind() == "block") {
                result.push(block);
            }
        }
        "block" if !static_ => result.push(node),
        _ => {}
    }
}
/// Static initialization owns a type declaration span; instance initialization
/// owns its body span. Their persisted procedure identities cannot collide.
pub fn initialization_name(node: Node<'_>) -> Option<&'static str> {
    if matches!(
        node.kind(),
        "class_declaration" | "interface_declaration" | "enum_declaration" | "record_declaration"
    ) {
        (!initialization_roots(node, true).is_empty()
            || node.child_by_field_name("superclass").is_some())
        .then_some("<clinit>")
    } else if matches!(node.kind(), "class_body" | "enum_body") {
        (!initialization_roots(node, false).is_empty()
            || node
                .parent()
                .is_some_and(|n| n.child_by_field_name("superclass").is_some()))
        .then_some("<instanceinit>")
    } else {
        None
    }
}
