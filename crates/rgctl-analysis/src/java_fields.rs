//! Java static fields reuse declaration storage; no synthetic object receiver.
use super::*;

pub(super) fn is_static_declaration(root: Node<'_>, at: OperandSpan) -> bool {
    let mut node = root.named_descendant_for_byte_range(at.start as usize, at.end as usize);
    while let Some(n) = node {
        if matches!(n.kind(), "field_declaration" | "constant_declaration") {
            return rgctl_plugin_helpers::java::is_static(n);
        }
        if is_class(n.kind()) {
            break;
        }
        node = n.parent();
    }
    false
}
fn class_name(mut node: Node<'_>, source: &[u8]) -> Option<String> {
    let mut names = Vec::new();
    loop {
        if matches!(
            node.kind(),
            "class_declaration"
                | "interface_declaration"
                | "enum_declaration"
                | "record_declaration"
        ) {
            names.push(
                node.child_by_field_name("name")?
                    .utf8_text(source)
                    .ok()?
                    .to_owned(),
            );
        }
        if let Some(parent) = node.parent() {
            node = parent
        } else {
            break;
        }
    }
    names.reverse();
    if names.is_empty() {
        return None;
    }
    let package = children(node)
        .into_iter()
        .find(|n| n.kind() == "package_declaration")
        .and_then(|n| {
            children(n)
                .into_iter()
                .find(|n| matches!(n.kind(), "identifier" | "scoped_identifier"))
        })
        .and_then(|n| n.utf8_text(source).ok());
    let owner = names.join(".");
    Some(
        package
            .filter(|p| !p.is_empty())
            .map_or(owner.clone(), |p| format!("{p}.{owner}")),
    )
}
/// Index only source-declared static fields. A receiver spelling alone never
/// proves a static access if a local/parameter declaration shadows that name.
#[allow(clippy::too_many_arguments)]
pub(super) fn index(
    root: Node<'_>,
    source: &[u8],
    ids: &HashMap<OperandSpan, Uuid>,
    decls: &[Declaration],
    stores: &HashMap<EnvironmentBinding, Vec<ValueRef>>,
    values: &HashMap<(Uuid, OperandSpan), ExpressionId>,
    limits: EnvironmentLimits,
    out: &mut EnvironmentFacts,
) -> Result<()> {
    let static_decls: Vec<_> = decls
        .iter()
        .filter(|d| d.field && is_static_declaration(root, d.at))
        .collect();
    for d in &static_decls {
        let Some(node) =
            root.named_descendant_for_byte_range(d.at.start as usize, d.at.end as usize)
        else {
            continue;
        };
        let Some(owner) = class_name(node, source) else {
            continue;
        };
        let binding = EnvironmentBinding {
            owner: d.owner,
            declaration: d.at,
        };
        out.exports.push(EnvironmentExport {
            name: format!("{owner}.{}", d.name),
            binding,
            values: stores.get(&binding).cloned().unwrap_or_default(),
        });
    }
    let imports: HashMap<_, _> = children(root)
        .into_iter()
        .filter(|n| n.kind() == "import_declaration")
        .filter_map(|n| {
            let text = n
                .utf8_text(source)
                .ok()?
                .trim()
                .trim_end_matches(';')
                .trim_start_matches("import")
                .trim();
            if text.starts_with("static ") || text.ends_with(".*") {
                return None;
            }
            Some((text.rsplit('.').next()?.to_owned(), text.to_owned()))
        })
        .collect();
    let mut declared_types = Vec::new();
    let mut work = vec![root];
    let mut visited = 0;
    while let Some(n) = work.pop() {
        visited += 1;
        if visited > limits.max_nodes {
            out.diagnostics.push(EnvironmentDiagnostic::LimitReached);
            break;
        }
        if matches!(
            n.kind(),
            "class_declaration"
                | "interface_declaration"
                | "enum_declaration"
                | "record_declaration"
        ) && let Some(name) = class_name(n, source)
        {
            declared_types.push(name);
        }
        work.extend(children(n));
    }
    let mut stack = vec![root];
    let mut count = 0;
    while let Some(node) = stack.pop() {
        count += 1;
        if count > limits.max_nodes
            || out.external_reads.len() + out.external_stores.len() > limits.max_checks
        {
            out.diagnostics.push(EnvironmentDiagnostic::LimitReached);
            break;
        }
        if node.kind() == "field_access"
            && let (Some(base), Some(field)) = (
                node.child_by_field_name("object"),
                node.child_by_field_name("field"),
            )
            && let (Ok(base_text), Ok(field_text)) =
                (base.utf8_text(source), field.utf8_text(source))
        {
            let at = span(base)?;
            // Explicit type names only; unresolved instance fields are handled
            // by receiver origins. Shadowed type names cannot be static proofs.
            let shadow = decls
                .iter()
                .any(|d| d.name == base_text && contains(d.scope, at));
            let own = class_name(node, source);
            let owner = if shadow {
                None
            } else if base_text == "this" {
                own
            } else if let Some(import) = imports.get(base_text) {
                Some(import.clone())
            } else {
                let mut types: Vec<_> = declared_types
                    .iter()
                    .filter(|name| {
                        name.as_str() == base_text || name.ends_with(&format!(".{base_text}"))
                    })
                    .cloned()
                    .collect();
                types.sort();
                types.dedup();
                if types.len() == 1 {
                    types.pop()
                } else if base_text.contains('.')
                    && base_text
                        .chars()
                        .all(|c| c.is_alphanumeric() || c == '.' || c == '_' || c == '$')
                {
                    Some(base_text.into())
                } else {
                    own.as_deref()
                        .and_then(|s| s.rsplit_once('.'))
                        .map(|(p, _)| format!("{p}.{base_text}"))
                }
            };
            if let Some(owner) = owner {
                let name = format!("{owner}.{field_text}");
                let function = procedure_owner(node, ids, Uuid::nil());
                let assignment = node.parent().filter(|n| {
                    n.kind() == "assignment_expression"
                        && n.child_by_field_name("left") == Some(node)
                });
                if let Some(assignment) = assignment {
                    let value = assignment
                        .child_by_field_name("right")
                        .and_then(|n| span(n).ok())
                        .and_then(|s| values.get(&(function, s)))
                        .map(|&expression| ValueRef {
                            function,
                            expression,
                        });
                    out.external_stores.push(EnvironmentExternalStore {
                        module: "@java".into(),
                        name,
                        value,
                    });
                } else if let Some(&expression) = values.get(&(function, span(node)?)) {
                    out.external_reads.push(EnvironmentExternalRead {
                        value: ValueRef {
                            function,
                            expression,
                        },
                        module: "@java".into(),
                        name,
                    });
                }
            }
        }
        stack.extend(children(node));
    }
    Ok(())
}
