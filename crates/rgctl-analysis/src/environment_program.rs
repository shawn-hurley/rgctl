//! Bind imported/same-package state to canonical source-module declarations.
use super::*;
use std::path::{Component, Path, PathBuf};

/// A module-level declaration and its modeled producer expressions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvironmentExport {
    /// Source-level exported/global name; resolution is scoped by module identity.
    pub name: String,
    /// Canonical owning declaration.
    pub binding: EnvironmentBinding,
    /// Possible explicit initializers/stores in that module.
    pub values: Vec<ValueRef>,
}
/// A source read of a named import or namespace member.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvironmentExternalRead {
    /// Exact native consumer.
    pub value: ValueRef,
    /// Literal source module name; @package means the same Go package/directory.
    pub module: String,
    /// Imported/exported name, including a selected namespace member.
    pub name: String,
}
/// Indexed module facts from an immutable repository-relative source file.
pub struct EnvironmentModule {
    /// Repository-relative source path; no filesystem lookup occurs in linking.
    pub path: String,
    /// Native source language.
    pub language: String,
    /// Module environment records.
    pub facts: EnvironmentFacts,
}
#[derive(Clone)]
pub(super) struct Import {
    pub(super) local: String,
    pub(super) module: String,
    pub(super) name: Option<String>,
    scope: OperandSpan,
}
fn unquote(s: &str) -> Option<String> {
    let s = s.trim();
    if s.contains('\\') {
        return None;
    }
    Some(s.trim_matches(['\'', '"', '`']).into())
}
pub(super) fn imports(
    root: Node<'_>,
    source: &[u8],
    language: &str,
    ids: &HashMap<OperandSpan, Uuid>,
    limit: usize,
) -> Result<Vec<Import>> {
    let root_span = span(root)?;
    let mut out = Vec::new();
    let mut stack = vec![root];
    let mut count = 0;
    while let Some(n) = stack.pop() {
        count += 1;
        if count > limit {
            break;
        }
        if matches!(language, "javascript" | "typescript") && n.kind() == "import_statement" {
            if let Some(module) = n
                .child_by_field_name("source")
                .and_then(|s| s.utf8_text(source).ok())
                .and_then(unquote)
            {
                let mut work = children(n);
                while let Some(part) = work.pop() {
                    if part.kind() == "import_specifier" {
                        if let Some(name) = part.child_by_field_name("name") {
                            let alias = part.child_by_field_name("alias").unwrap_or(name);
                            out.push(Import {
                                local: alias.utf8_text(source)?.into(),
                                module: module.clone(),
                                name: Some(name.utf8_text(source)?.into()),
                                scope: root_span,
                            });
                        }
                    } else if part.kind() == "namespace_import" {
                        if let Some(alias) = part.named_child(0) {
                            out.push(Import {
                                local: alias.utf8_text(source)?.into(),
                                module: module.clone(),
                                name: None,
                                scope: root_span,
                            });
                        }
                    } else if part.kind() == "import_clause" {
                        for child in children(part) {
                            if child.kind() == "identifier" {
                                out.push(Import {
                                    local: child.utf8_text(source)?.into(),
                                    module: module.clone(),
                                    name: Some("default".into()),
                                    scope: root_span,
                                });
                            } else {
                                work.push(child);
                            }
                        }
                    } else {
                        work.extend(children(part));
                    }
                }
            }
        } else if language == "python"
            && matches!(n.kind(), "import_from_statement" | "import_statement")
        {
            let from = n
                .child_by_field_name("module_name")
                .map(|m| m.utf8_text(source))
                .transpose()?;
            let mut cursor = n.walk();
            for part in n.children_by_field_name("name", &mut cursor) {
                let name = part.child_by_field_name("name").unwrap_or(part);
                let alias = part.child_by_field_name("alias").unwrap_or(name);
                let (scope, _) = lexical_scope(alias, language, true, ids, root_span);
                let text = name.utf8_text(source)?;
                out.push(Import {
                    local: alias.utf8_text(source)?.into(),
                    module: from.unwrap_or(text).into(),
                    name: from.map(|_| text.into()),
                    scope,
                });
            }
        } else if language == "go" && n.kind() == "import_spec" {
            if let Some(module) = n
                .child_by_field_name("path")
                .and_then(|s| s.utf8_text(source).ok())
                .and_then(unquote)
            {
                let local = n
                    .child_by_field_name("name")
                    .map(|n| n.utf8_text(source))
                    .transpose()?
                    .map(str::to_owned)
                    .unwrap_or_else(|| module.rsplit('/').next().unwrap_or(&module).into());
                if !matches!(&*local, "_" | ".") {
                    out.push(Import {
                        local,
                        module,
                        name: None,
                        scope: root_span,
                    });
                }
            }
        }
        stack.extend(children(n));
    }
    Ok(out)
}
pub(super) fn imported<'a>(name: &str, at: OperandSpan, items: &'a [Import]) -> Option<&'a Import> {
    items
        .iter()
        .filter(|i| i.local == name && contains(i.scope, at))
        .min_by_key(|i| i.scope.end - i.scope.start)
}
fn normalized(path: &Path) -> String {
    let mut result = PathBuf::new();
    for part in path.components() {
        match part {
            Component::CurDir => {}
            Component::ParentDir => {
                if !result.pop() {
                    return "<outside-source-root>".into();
                }
            }
            Component::Normal(v) => result.push(v),
            _ => {}
        }
    }
    result.to_string_lossy().replace('\\', "/")
}
fn candidates(from: &EnvironmentModule, module: &str, files: &[EnvironmentModule]) -> Vec<usize> {
    let parent = Path::new(&from.path).parent().unwrap_or(Path::new(""));
    if module == "@package" {
        return files
            .iter()
            .enumerate()
            .filter(|(_, f)| {
                f.language == "go"
                    && f.facts.package_name == from.facts.package_name
                    && Path::new(&f.path).parent() == Some(parent)
            })
            .map(|(i, _)| i)
            .collect();
    }
    let mut names = Vec::new();
    if matches!(&*from.language, "javascript" | "typescript") {
        if !module.starts_with('.') {
            return Vec::new();
        }
        let path = normalized(&parent.join(module));
        names.push(path.clone());
        for suffix in ["js", "jsx", "ts", "tsx"] {
            names.push(format!("{path}.{suffix}"));
            names.push(format!("{path}/index.{suffix}"));
        }
        if path.ends_with(".js") {
            names.push(format!("{}.ts", path.trim_end_matches(".js")));
        }
    } else if from.language == "python" {
        let dots = module.chars().take_while(|&c| c == '.').count();
        let mut base = if dots > 0 {
            parent.to_path_buf()
        } else {
            PathBuf::new()
        };
        for _ in 1..dots {
            base.pop();
        }
        let path = normalized(&base.join(module.trim_start_matches('.').replace('.', "/")));
        names.push(format!("{path}.py"));
        names.push(format!("{path}/__init__.py"));
    } else if from.language == "go" {
        // Exact repository-relative import paths only; external module prefixes need
        // a resolver-supplied canonical package map rather than a basename guess.
        names.push(format!("{module}/"));
    }
    files
        .iter()
        .enumerate()
        .filter(|(_, f)| {
            names
                .iter()
                .any(|n| f.path == *n || (from.language == "go" && f.path.starts_with(n)))
        })
        .map(|(i, _)| i)
        .collect()
}
/// Join already indexed source modules without reparsing or filesystem access.
/// Unknown external packages/exports remain diagnostics, never a successful negative.
pub fn link_environment_modules(files: Vec<EnvironmentModule>, limit: usize) -> EnvironmentFacts {
    let mut out = EnvironmentFacts::default();
    let mut checks = 0usize;
    let mut satisfied = HashSet::new();
    let mut resolved_modules: HashMap<(usize, String), Vec<usize>> = HashMap::new();
    for (from_index, from) in files.iter().enumerate() {
        for read in &from.facts.external_reads {
            if checks >= limit {
                break;
            }
            checks += 1;
            let mut matched = false;
            let modules = resolved_modules
                .entry((from_index, read.module.clone()))
                .or_insert_with(|| candidates(from, &read.module, &files));
            for &i in modules.iter() {
                for export in files[i]
                    .facts
                    .exports
                    .iter()
                    .filter(|e| e.name == read.name)
                {
                    for &value in &export.values {
                        if checks >= limit {
                            break;
                        }
                        checks += 1;
                        matched = true;
                        if value != read.value {
                            out.transfers.push(EnvironmentTransfer {
                                binding: export.binding,
                                from: value,
                                to: read.value,
                            });
                        }
                    }
                }
            }
            if matched {
                satisfied.insert(read.value);
            } else {
                out.diagnostics
                    .push(EnvironmentDiagnostic::UnresolvedImport {
                        value: read.value,
                        module: read.module.clone(),
                        name: read.name.clone(),
                    });
            }
        }
    }
    for mut file in files {
        if out.transfers.len() + file.facts.transfers.len() > limit
            || out.member_reads.len() + file.facts.member_reads.len() > limit
            || out.callables.len() + file.facts.callables.len() > limit
            || out.diagnostics.len() + file.facts.diagnostics.len() > limit
        {
            out.diagnostics.push(EnvironmentDiagnostic::LimitReached);
        }
        file.facts
            .transfers
            .truncate(limit.saturating_sub(out.transfers.len()));
        file.facts
            .member_reads
            .truncate(limit.saturating_sub(out.member_reads.len()));
        file.facts
            .callables
            .truncate(limit.saturating_sub(out.callables.len()));
        file.facts
            .diagnostics
            .truncate(limit.saturating_sub(out.diagnostics.len()));
        out.transfers.extend(file.facts.transfers);
        out.member_reads.extend(file.facts.member_reads);
        out.callables.extend(file.facts.callables);
        out.diagnostics.extend(file.facts.diagnostics.into_iter().filter(|d|!matches!(d,EnvironmentDiagnostic::UnresolvedRead{value,..} if satisfied.contains(value))));
    }
    if checks >= limit {
        out.diagnostics.push(EnvironmentDiagnostic::LimitReached);
    }
    out.transfers.sort_by_key(|t| {
        (
            t.binding.owner,
            t.binding.declaration.start,
            t.from.function,
            t.from.expression.0,
            t.to.function,
            t.to.expression.0,
        )
    });
    out
}
