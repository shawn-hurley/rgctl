use rgctl_extraction::{Extractor, GraphBuilder, facts_cache::FactsCache};
use rgctl_graph::schema::{EdgeType, NodeType};
use rgctl_plugin_api::{LanguagePlugin, SymbolType};
use std::{path::Path, sync::Arc};

type Case = (
    Arc<dyn LanguagePlugin>,
    &'static str,
    &'static str,
    &'static str,
);
fn plugins() -> Vec<Case> {
    let registry = rgctl_languages::default_registry();
    vec![
        (
            "javascript",
            "src/app.js",
            "function helper(){return 1;} function exercise(){return helper();}",
            "src.app",
        ),
        (
            "typescript",
            "src/app.ts",
            "function helper():number{return 1;} function exercise():number{return helper();}",
            "src.app",
        ),
        (
            "python",
            "src/app.py",
            "def helper():\n    return 1\ndef exercise():\n    return helper()\n",
            "src.app",
        ),
        (
            "go",
            "src/app.go",
            "package demo\nfunc helper() int {return 1}\nfunc exercise() int {return helper()}\n",
            "demo",
        ),
    ]
    .into_iter()
    .map(|(language, path, source, module)| {
        (
            registry.get_language_plugin(language).unwrap(),
            path,
            source,
            module,
        )
    })
    .collect()
}

#[test]
fn public_extraction_entry_points_agree_on_names_and_call_endpoints() {
    for (plugin, path, source, module) in plugins() {
        let all = plugin
            .extract_all(Path::new(path), source.as_bytes())
            .unwrap();
        let symbols = plugin
            .extract_symbols(Path::new(path), source.as_bytes())
            .unwrap();
        for name in ["helper", "exercise"] {
            for list in [&all.symbols, &symbols] {
                let symbol = list
                    .iter()
                    .find(|s| s.name == name && s.symbol_type == SymbolType::Function)
                    .unwrap();
                assert_eq!(
                    symbol.qualified_name.as_deref(),
                    Some(format!("{module}.{name}").as_str()),
                    "{}",
                    plugin.language_id()
                );
            }
        }
        let relations = plugin
            .extract_relations(Path::new(path), source.as_bytes(), &symbols)
            .unwrap();
        for list in [&all.relations, &relations] {
            assert!(
                list.iter().any(|r| r.from == format!("{module}.exercise")
                    && (r.to_qualified_hint.as_deref()
                        == Some(format!("{module}.helper").as_str())
                        || r.to == format!("{module}.helper"))),
                "{}: {list:?}",
                plugin.language_id()
            );
        }
    }
}

#[test]
fn logical_modules_survive_checkout_moves_and_cache_reuse() {
    let cache = Arc::new(FactsCache::new());
    let source = b"function helper(){return 1;} function exercise(){return helper();}";
    let registry = Arc::new(rgctl_languages::default_registry());
    for root in ["/checkout/baseline", "/different/candidate"] {
        let extractor = Extractor::new(registry.clone())
            .with_repo_root(root)
            .with_facts_cache(cache.clone());
        for directory in ["first", "second"] {
            let path = Path::new(root).join(directory).join("app.js");
            let file = extractor
                .extract_file_with_source(&path, source.to_vec())
                .unwrap();
            let exercise = file.symbols.iter().find(|s| s.name == "exercise").unwrap();
            assert_eq!(
                exercise.qualified_name.as_deref(),
                Some(format!("{directory}.app.exercise").as_str())
            );
            let mut builder = GraphBuilder::new();
            extractor.populate_graph(&[file], &mut builder).unwrap();
            let (nodes, edges) = builder.into_graph();
            let find = |name: &str| {
                nodes
                    .iter()
                    .find(|n| n.node_type == NodeType::Function && &*n.name == name)
                    .unwrap()
                    .id
            };
            assert!(edges.iter().any(|e| e.from == find("exercise")
                && e.to == find("helper")
                && e.edge_type == EdgeType::Calls));
        }
    }
}

#[test]
fn python_package_init_and_nested_functions_have_lexical_owners() {
    let plugin = rgctl_languages::default_registry()
        .get_language_plugin("python")
        .unwrap();
    let all = plugin
        .extract_all(
            Path::new("pkg/__init__.py"),
            b"def outer():\n    def inner():\n        return 1\n    return inner()\n",
        )
        .unwrap();
    let names: Vec<_> = all
        .symbols
        .iter()
        .filter_map(|s| s.qualified_name.as_deref())
        .collect();
    assert!(names.contains(&"pkg.outer"), "{names:?}");
    assert!(names.contains(&"pkg.outer.inner"), "{names:?}");
}
