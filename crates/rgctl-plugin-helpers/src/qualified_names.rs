//! Names for declarations whose language extractor has no explicit owner name.
//! Physical checkout roots never participate in the namespace.
use rgctl_plugin_api::{Relation, Symbol, SymbolType};
use std::{
    collections::HashMap,
    path::{Component, Path},
};

/// File module for standalone extraction. Absolute callers without a repository
/// context get the file stem; the extraction worker supplies the logical path.
pub fn file_module(path: &Path, python: bool) -> String {
    let path = if path.is_absolute() {
        Path::new(path.file_name().unwrap_or_default())
    } else {
        path
    };
    let mut parts: Vec<String> = path
        .with_extension("")
        .components()
        .filter_map(|c| {
            if let Component::Normal(s) = c {
                Some(s.to_string_lossy().into_owned())
            } else {
                None
            }
        })
        .collect();
    if python && parts.last().is_some_and(|p| p == "__init__") && parts.len() > 1 {
        parts.pop();
    }
    parts.join(".")
}

fn scope(symbol: &Symbol) -> bool {
    matches!(
        symbol.symbol_type,
        SymbolType::Function
            | SymbolType::Method
            | SymbolType::Class
            | SymbolType::Struct
            | SymbolType::Interface
            | SymbolType::Enum
    )
}

/// Qualify using an already parsed tree; never starts a second parser.
pub fn qualify_file(
    language: &str,
    path: &Path,
    root: tree_sitter::Node<'_>,
    source: &[u8],
    symbols: &mut [Symbol],
    relations: &mut [Relation],
) {
    let module = if language == "go" {
        root.named_children(&mut root.walk())
            .find(|n| n.kind() == "package_clause")
            .and_then(|n| n.named_child(0))
            .and_then(|n| n.utf8_text(source).ok())
            .unwrap_or("package")
            .to_owned()
    } else {
        file_module(path, language == "python")
    };
    qualify(&module, symbols, relations);
}
fn contains(outer: &Symbol, inner: &Symbol) -> bool {
    let a = &outer.location;
    let b = &inner.location;
    let start = (a.start_line, a.start_column);
    let end = (a.end_line, a.end_column);
    start <= (b.start_line, b.start_column)
        && (b.end_line, b.end_column) <= end
        && (start, end) != ((b.start_line, b.start_column), (b.end_line, b.end_column))
}

/// Fill absent declaration names without changing existing explicit owner names
/// or callable discriminators. Rewrite local relation endpoints with the names.
pub fn qualify(module: &str, symbols: &mut [Symbol], relations: &mut [Relation]) {
    if module.is_empty() {
        return;
    }
    let mut order: Vec<_> = (0..symbols.len())
        .filter(|&i| {
            scope(&symbols[i])
                || matches!(
                    symbols[i].symbol_type,
                    SymbolType::Variable | SymbolType::TypeAlias
                )
        })
        .collect();
    order.sort_by_key(|&i| {
        let p = &symbols[i].location;
        (
            p.start_line,
            p.start_column,
            std::cmp::Reverse(p.end_line),
            std::cmp::Reverse(p.end_column),
        )
    });
    let mut stack: Vec<usize> = Vec::new();
    let mut aliases: HashMap<String, Vec<usize>> = HashMap::new();
    for i in order {
        while stack
            .last()
            .is_some_and(|&p| !contains(&symbols[p], &symbols[i]))
        {
            stack.pop();
        }
        let old = symbols[i].qualified_name.clone();
        if old.is_none() {
            let owner = stack
                .last()
                .and_then(|&p| symbols[p].qualified_name.as_deref())
                .unwrap_or(module);
            let name = format!("{owner}.{}", symbols[i].name);
            symbols[i].qualified_name = Some(name);
            symbols[i].metadata["module_namespace"] = module.into();
        } else if let Some(previous) = symbols[i]
            .metadata
            .get("module_namespace")
            .and_then(|v| v.as_str())
        {
            if previous != module {
                if let Some(suffix) = old
                    .as_deref()
                    .and_then(|s| s.strip_prefix(previous))
                    .and_then(|s| s.strip_prefix('.'))
                {
                    symbols[i].qualified_name = Some(format!("{module}.{suffix}"));
                    symbols[i].metadata["module_namespace"] = module.into();
                }
            }
        }
        if symbols[i].metadata.get("module_namespace").is_some() {
            aliases.entry(symbols[i].name.clone()).or_default().push(i);
            if let Some(old) = old {
                aliases.entry(old).or_default().push(i);
            }
        }
        if scope(&symbols[i]) {
            stack.push(i);
        }
    }
    for relation in relations {
        if let Some(candidates) = aliases.get(&relation.from) {
            let mut matches = candidates.iter().copied().filter(|&i| {
                let s = &symbols[i];
                let p = &s.location;
                let r = &relation.location;
                p.file == r.file
                    && (p.start_line, p.start_column) <= (r.start_line, r.start_column)
                    && (r.end_line, r.end_column) <= (p.end_line, p.end_column)
                    && relation
                        .metadata
                        .get("from_identity_discriminator")
                        .and_then(|v| v.as_str())
                        .is_none_or(|identity| {
                            s.metadata
                                .get("identity_discriminator")
                                .and_then(|v| v.as_str())
                                .unwrap_or("")
                                == identity
                        })
            });
            if let Some(index) = matches.next() {
                if matches.next().is_none() {
                    if let Some(name) = &symbols[index].qualified_name {
                        relation.from = name.clone();
                    }
                }
            }
        }
        // A shared owner/name may have distinct callable identities. Rewriting
        // that common name does not select an overload or a superseded body.
        {
            let hint = relation.to_qualified_hint.as_ref().unwrap_or(&relation.to);
            if let Some(candidates) = aliases.get(hint) {
                let unique = candidates.first().copied().filter(|i| {
                    candidates
                        .iter()
                        .all(|&x| symbols[x].qualified_name == symbols[*i].qualified_name)
                });
                if let Some(i) = unique {
                    relation.to_qualified_hint = symbols[i].qualified_name.clone();
                }
            }
        }
    }
}

/// Upgrade standalone namespaces to a repository-relative namespace after a
/// raw facts-cache hit or extraction. No filesystem discovery is performed.
pub fn qualify_in_repo(
    language: &str,
    logical_path: &Path,
    symbols: &mut [Symbol],
    relations: &mut [Relation],
) {
    let module = match language {
        "javascript" | "typescript" => file_module(logical_path, false),
        "python" => file_module(logical_path, true),
        "go" => {
            if logical_path.is_absolute() {
                return;
            }
            let Some(package) = symbols
                .iter()
                .find_map(|s| s.metadata.get("module_namespace").and_then(|v| v.as_str()))
            else {
                return;
            };
            let parent = logical_path.parent().unwrap_or_else(|| Path::new(""));
            let directory = parent
                .components()
                .filter_map(|c| {
                    if let Component::Normal(s) = c {
                        Some(s.to_string_lossy())
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>()
                .join(".");
            if directory.is_empty()
                || directory == package
                || directory.ends_with(&format!(".{package}"))
            {
                if directory.is_empty() {
                    package.to_owned()
                } else {
                    directory
                }
            } else {
                format!("{directory}.{package}")
            }
        }
        _ => return,
    };
    qualify(&module, symbols, relations);
}
