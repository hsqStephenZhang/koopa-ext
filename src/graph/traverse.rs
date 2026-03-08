use std::collections::HashSet;

use crate::graph::graph::{DirectedGraph, Successors};

/// Computes the reverse post-order (RPO) of a directed graph starting from a given node.
///
/// # Arguments
/// * `graph` - The directed graph to traverse
/// * `start_node` - The entry/starting node for traversal
///
/// # Returns
/// A vector of nodes in reverse post-order
pub fn reverse_post_order<G: DirectedGraph + Successors>(
    graph: &G,
    start_node: G::Node,
) -> Vec<G::Node> {
    let mut post_order = post_order(graph, start_node);
    post_order.reverse();
    post_order
}

/// Computes the post-order traversal of a directed graph starting from a given node.
///
/// # Arguments
/// * `graph` - The directed graph to traverse
/// * `start_node` - The entry/starting node for traversal
///
/// # Returns
/// A vector of nodes in post-order
pub fn post_order<G: DirectedGraph + Successors>(graph: &G, start_node: G::Node) -> Vec<G::Node> {
    let mut post_ordering = Vec::with_capacity(graph.num_nodes());
    let mut visited = HashSet::new();
    post_order_dfs(graph, &mut post_ordering, &mut visited, start_node);
    post_ordering
}

fn post_order_dfs<G: DirectedGraph + Successors>(
    graph: &G,
    post_ordering: &mut Vec<G::Node>,
    visited: &mut HashSet<G::Node>,
    cur: G::Node,
) {
    if !visited.insert(cur) {
        return;
    }

    for succ in graph.succs(cur) {
        post_order_dfs(graph, post_ordering, visited, succ);
    }

    post_ordering.push(cur);
}
