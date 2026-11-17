//! Shared names for native Go function literals.
use std::collections::HashMap;
use tree_sitter::Node;

/// Assign literal ordinals in one preorder pass. Each callable owns a separate
/// ordinal namespace; source offsets never participate in the symbol spelling.
/// Missing entries after the syntax budget remain unsupported rather than guessed.
pub fn literal_names(root: Node<'_>) -> HashMap<usize, String> {
    let mut names = HashMap::new();
    let mut counters = vec![0usize];
    let mut stack = vec![(root, false, 0usize)];
    let mut visited = 0usize;
    while let Some((node, leave, depth)) = stack.pop() {
        if leave {
            counters.pop();
            continue;
        }
        visited += 1;
        if visited > 1_000_000 || depth > 2048 {
            continue;
        }
        let callable = matches!(
            node.kind(),
            "function_declaration" | "method_declaration" | "func_literal"
        );
        if node.kind() == "func_literal"
            && let Some(next) = counters.last_mut()
        {
            names.insert(node.id(), format!("$lambda${next}"));
            *next += 1;
        }
        if callable {
            counters.push(0);
            stack.push((node, true, depth));
        }
        let start = stack.len();
        let mut c = node.walk();
        stack.extend(node.named_children(&mut c).map(|n| (n, false, depth + 1)));
        stack[start..].reverse();
    }
    names
}
