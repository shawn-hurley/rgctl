//! Conservative source inventories for consumer-supplied receiver-query premises.
use crate::cfg_builder::ParsedSourceFile;
use crate::operands::OperandSpan;
use std::collections::{HashMap, HashSet};

/// Literal nominal type spelling at one exact Go composite allocation.
#[derive(Debug)]
pub struct NominalAllocation {
    /// Exact complete composite literal range, matching its native result value.
    pub span: OperandSpan,
    /// Syntactic qualified type spelling, not an inferred structural type.
    pub type_name: String,
}
/// Native declaration/source guards, separate from the graph identity resolver.
#[derive(Debug, Default)]
pub struct ReceiverScopeFacts {
    /// Ordinary free/static declarations eligible for exact direct target resolution.
    pub direct_functions: Vec<OperandSpan>,
    /// Internal direct-only function declarations, identified by exact source span.
    pub private_functions: Vec<OperandSpan>,
    /// Exact Go allocation/type syntax for canonical graph resolution.
    pub nominal_allocations: Vec<NominalAllocation>,
    /// Constructorless, fieldless TS classes and empty Go struct declarations.
    pub trivial_types: Vec<OperandSpan>,
    /// Names used as values or selectors outside ordinary direct invocation syntax.
    /// Consumers must reject escaped function bindings across all selected files.
    pub value_names: HashSet<String>,
    /// Names declared more than once in this source inventory.
    pub shadowed_names: HashSet<String>,
    /// Assignment/update/delete syntax can rebind TS class/prototype identities.
    pub dynamic_writes: bool,
    /// Traversal budget exhausted; no premises from this inventory are admissible.
    pub limited: bool,
}
fn span(n: tree_sitter::Node<'_>) -> Option<OperandSpan> {
    Some(OperandSpan {
        start: n.start_byte().try_into().ok()?,
        end: n.end_byte().try_into().ok()?,
    })
}
/// Reuse a cached native parse. The result does not resolve imports or canonical
/// symbols; consumers must combine it with graph-qualified source identities.
pub fn receiver_scope_facts(
    parsed: &ParsedSourceFile,
    source: &[u8],
    language: &str,
    max_nodes: usize,
) -> ReceiverScopeFacts {
    let mut out = ReceiverScopeFacts::default();
    let mut pending = vec![parsed.tree().root_node()];
    let mut seen = 0;
    let mut declarations: HashMap<String, usize> = HashMap::new();
    while let Some(n) = pending.pop() {
        seen += 1;
        if seen > max_nodes {
            out.limited = true;
            return out;
        }
        if matches!(
            n.kind(),
            "assignment_expression"
                | "augmented_assignment_expression"
                | "update_expression"
                | "delete_expression"
        ) {
            out.dynamic_writes = true;
        }
        if matches!(
            n.kind(),
            "class_declaration"
                | "class_definition"
                | "function_declaration"
                | "function_definition"
                | "method_declaration"
                | "type_spec"
                | "variable_declarator"
                | "formal_parameter"
                | "required_parameter"
                | "optional_parameter"
                | "parameter_declaration"
                | "import_specifier"
                | "catch_clause"
        ) && let Some(binding) = n
            .child_by_field_name("alias")
            .or_else(|| n.child_by_field_name("name"))
            .or_else(|| n.child_by_field_name("pattern"))
            .or_else(|| n.child_by_field_name("parameter"))
        {
            let mut patterns = vec![binding];
            while let Some(binding) = patterns.pop() {
                if matches!(
                    binding.kind(),
                    "identifier"
                        | "type_identifier"
                        | "field_identifier"
                        | "shorthand_property_identifier_pattern"
                ) {
                    if let Ok(name) = binding.utf8_text(source) {
                        let count = declarations.entry(name.to_owned()).or_default();
                        *count += 1;
                        if *count > 1 {
                            out.shadowed_names.insert(name.to_owned());
                            out.value_names.insert(name.to_owned());
                        }
                    }
                } else {
                    let mut cursor = binding.walk();
                    patterns.extend(binding.named_children(&mut cursor));
                }
            }
        }
        if matches!(n.kind(), "identifier" | "field_identifier") {
            let parent = n.parent();
            let declaration = parent.is_some_and(|p| {
                matches!(
                    p.kind(),
                    "function_declaration"
                        | "function_definition"
                        | "method_declaration"
                        | "class_declaration"
                        | "class_definition"
                        | "type_spec"
                        | "variable_declarator"
                        | "formal_parameter"
                        | "required_parameter"
                        | "parameter_declaration"
                        | "type_parameter"
                ) && p
                    .child_by_field_name("name")
                    .is_some_and(|v| v.id() == n.id())
            });
            let mut head = n;
            if let Some(p) = parent
                && matches!(
                    p.kind(),
                    "generic_function" | "instantiation_expression" | "generic_type"
                )
            {
                head = p;
            }
            let direct = head.parent().is_some_and(|p| {
                (matches!(p.kind(), "call_expression" | "call")
                    && p.child_by_field_name("function")
                        .is_some_and(|v| v.id() == head.id()))
                    || (p.kind() == "method_invocation"
                        && p.child_by_field_name("name")
                            .is_some_and(|v| v.id() == head.id())
                        && p.child_by_field_name("object").is_none())
            });
            if !declaration
                && !direct
                && let Ok(name) = n.utf8_text(source)
            {
                out.value_names.insert(name.to_owned());
            }
        }
        if language == "go"
            && n.kind() == "composite_literal"
            && let Some(ty) = n.child_by_field_name("type")
            && matches!(ty.kind(), "qualified_type" | "type_identifier")
            && let Ok(text) = ty.utf8_text(source)
            && text
                .chars()
                .all(|c| c.is_alphanumeric() || matches!(c, '_' | '.'))
            && let Some(span) = span(n)
        {
            out.nominal_allocations.push(NominalAllocation {
                span,
                type_name: text.to_owned(),
            });
        }
        let private = match language {
            "java" if n.kind() == "method_declaration" => {
                let mut cursor = n.walk();
                let modifiers = n
                    .named_children(&mut cursor)
                    .find(|c| c.kind() == "modifiers");
                modifiers.is_some_and(|m| {
                    let text = m.utf8_text(source).unwrap_or("");
                    !text.contains('@')
                        && text.split_whitespace().any(|w| w == "static")
                        && !text
                            .split_whitespace()
                            .any(|w| matches!(w, "public" | "protected"))
                })
            }
            "typescript" if n.kind() == "function_declaration" => {
                !n.parent().is_some_and(|p| p.kind() == "export_statement")
            }
            "go" if n.kind() == "function_declaration" => n
                .child_by_field_name("name")
                .and_then(|v| v.utf8_text(source).ok())
                .and_then(|s| s.chars().next())
                .is_some_and(|c| c.is_lowercase()),
            _ => false,
        };
        let direct = match language {
            "java" if n.kind() == "method_declaration" => {
                let mut c = n.walk();
                n.named_children(&mut c)
                    .find(|v| v.kind() == "modifiers")
                    .is_some_and(|m| {
                        m.utf8_text(source)
                            .unwrap_or("")
                            .split_whitespace()
                            .any(|w| w == "static")
                    })
            }
            "typescript" | "go" => n.kind() == "function_declaration",
            "javascript" => {
                n.kind() == "function_declaration"
                    && !n.children(&mut n.walk()).any(|n| n.kind() == "async")
            }
            "python" => {
                n.kind() == "function_definition"
                    && !n.parent().is_some_and(|p| {
                        p.kind() == "decorated_definition"
                            || p.parent().is_some_and(|n| n.kind() == "class_definition")
                    })
                    && !n.children(&mut n.walk()).any(|n| n.kind() == "async")
            }
            _ => false,
        };
        if direct && let Some(s) = span(n) {
            out.direct_functions.push(s);
        }
        if private && let Some(s) = span(n) {
            out.private_functions.push(s);
        }
        if language == "typescript" && n.kind() == "class_declaration" {
            let mut c = n.walk();
            let children: Vec<_> = n.named_children(&mut c).collect();
            let simple_header = children.iter().all(|v| {
                matches!(
                    v.kind(),
                    "type_identifier"
                        | "identifier"
                        | "class_body"
                        | "type_parameters"
                        | "class_heritage"
                )
            }) && !children.iter().any(|v| {
                v.kind() == "class_heritage" && {
                    let mut c = v.walk();
                    v.named_children(&mut c)
                        .any(|x| x.kind() == "extends_clause")
                }
            });
            let trivial = n.child_by_field_name("body").is_some_and(|body| {
                let mut c = body.walk();
                body.named_children(&mut c).all(|v| {
                    v.kind() == "comment"
                        || (v.kind() == "method_definition"
                            && {
                                let mut c = v.walk();
                                !v.children(&mut c)
                                    .any(|x| matches!(x.kind(), "get" | "set"))
                            }
                            && v.child_by_field_name("name").is_some_and(|name| {
                                matches!(name.kind(), "property_identifier" | "identifier")
                                    && name.utf8_text(source).ok() != Some("constructor")
                            })
                            && {
                                let mut c = v.walk();
                                !v.named_children(&mut c).any(|x| x.kind() == "decorator")
                            })
                })
            });
            if simple_header
                && trivial
                && let Some(s) = span(n)
            {
                out.trivial_types.push(s);
            }
        }
        if language == "go"
            && n.kind() == "type_spec"
            && let Some(ty) = n.child_by_field_name("type")
            && ty.kind() == "struct_type"
        {
            let mut c = ty.walk();
            let empty = ty.named_children(&mut c).all(|v| {
                let mut c = v.walk();
                v.named_children(&mut c).all(|x| x.kind() == "comment")
            });
            if empty && let Some(s) = span(n) {
                out.trivial_types.push(s);
            }
        }
        let mut cursor = n.walk();
        pending.extend(n.named_children(&mut cursor));
    }
    out
}

#[cfg(test)]
#[path = "receiver_scope_tests.rs"]
mod tests;
