use std::collections::HashSet;

use crate::graph::graph::{DirectedGraph, Successors};

/// compute the RPO(reverse post ordering) of a given Graph and start(entry) node
pub fn rpo<G: DirectedGraph + Successors>(graph: &G, start_node: G::Node) -> Vec<G::Node> {
    let mut post_ordering = Vec::with_capacity(graph.num_nodes());
    let mut visited = HashSet::new();
    post_order(graph, &mut post_ordering, &mut visited, start_node);
    post_ordering.reverse();
    post_ordering
}

fn post_order<G: DirectedGraph + Successors>(
    graph: &G,
    post_ordering: &mut Vec<G::Node>,
    visited: &mut HashSet<G::Node>,
    cur: G::Node,
) {
    if !visited.insert(cur) {
        return;
    }

    for succ in graph.succs(cur) {
        post_order(graph, post_ordering, visited, succ);
    }

    post_ordering.push(cur);
}
