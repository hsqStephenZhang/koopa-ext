use std::collections::{BTreeMap, HashMap};
use std::fmt::{Debug, Display};
use std::hash::Hash;

use crate::graph::dom_tree::DomTree;
use crate::graph::traverse::reverse_post_order;
use crate::graph::{DirectedGraph, Graph};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Loop(u32);

impl Loop {
    pub fn new(index: u32) -> Self {
        Loop(index)
    }

    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl Display for Loop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(core::format_args!(concat!("loop", "{}"), self.0))
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct LoopData<N> {
    /// header of the loop
    header: N,
    /// it's parent loop
    parent: Option<Loop>,
    /// level of the loop
    level: usize,
}

impl<N: Clone + Copy> LoopData<N> {
    pub fn new(header: N, parent: Option<Loop>) -> Self {
        Self { header, parent, level: 1 }
    }

    pub fn header(&self) -> N {
        self.header
    }

    pub fn parent(&self) -> Option<Loop> {
        self.parent
    }
}

pub struct LoopsAnalysis<N> {
    /// from loop's id to it's actual data
    loops: BTreeMap<Loop, LoopData<N>>,
    /// basic block to the inner most loop
    bb_to_loop: HashMap<N, Loop>,

    next_loop_id: u32,
}

impl<N> Default for LoopsAnalysis<N> {
    fn default() -> Self {
        Self { loops: Default::default(), bb_to_loop: Default::default(), next_loop_id: 0 }
    }
}

impl<N: PartialEq + Eq + Hash + Copy + Debug> LoopsAnalysis<N> {
    pub fn new() -> Self {
        Self::default()
    }

    fn next_id(&mut self) -> Loop {
        let id = self.next_loop_id;
        self.next_loop_id += 1;
        Loop::new(id)
    }

    pub fn loops(&self) -> &BTreeMap<Loop, LoopData<N>> {
        &self.loops
    }

    pub fn bb_to_loop(&self) -> &HashMap<N, Loop> {
        &self.bb_to_loop
    }

    pub fn loop_of(&self, bb: N) -> Option<Loop> {
        self.bb_to_loop.get(&bb).copied()
    }

    pub fn compute<G: DirectedGraph<Node = N> + Graph>(
        &mut self,
        graph: &G,
        start_node: N,
        dom_tree: &DomTree<N>,
    ) {
        let rpo: Vec<N> = reverse_post_order(graph, start_node);
        let loops = rpo
            .iter()
            .filter(|b| Self::is_loop_header(graph, **b, dom_tree))
            .cloned()
            .collect::<Vec<_>>();

        for lp in &loops {
            let cur_loop_num = self.next_id();
            self.loops.insert(cur_loop_num, LoopData::new(*lp, None));
        }

        let keys = self.loops.keys().copied().collect::<Vec<_>>();

        // start from the inner loop
        for &cur_loop_num in keys.iter().rev() {
            let header = self.loops[&cur_loop_num].header;
            // each block belongs to a deepest loop or doesn't belong to any at all
            // we perform reverse-dfs(iterate the preds rather than succ)
            // to collect the body of current loop and tag the loop that it belongs to it

            // init with all the latches
            let mut stack = graph
                .preds(header)
                .filter(|pred| dom_tree.dominates(header, *pred))
                .collect::<Vec<_>>();

            while !stack.is_empty() {
                let mut next = None;
                let cur = stack.pop().unwrap();

                match self.bb_to_loop.get(&cur).copied() {
                    None => {
                        self.bb_to_loop.insert(cur, cur_loop_num);
                        next = Some(cur);
                    }
                    Some(mut subloop_num) => {
                        // cur node is already visited
                        // there are two situations
                        //  1. it's the current loop. we have already visited it and tag the loop num for it.
                        //  2. it's a subloop. we must skip the body of the subloop by jumping to it's header

                        // if we have three loops l1 <- l2 <- l3
                        // l2 and l3 has already been handled
                        // then l3's parent is set, but l2's parent is not
                        // when we are handling l1
                        // we might encounter a latch that belongs to l3
                        // but we must start from l2's header and set l2's parent index
                        //
                        // so we must find the first subloop whose parent idnex is still unset
                        while let Some(p) = self.loops.get(&subloop_num).unwrap().parent {
                            if p == cur_loop_num {
                                break;
                            } else {
                                subloop_num = p;
                            }
                        }

                        if subloop_num != cur_loop_num {
                            let subloop = self.loops.get_mut(&subloop_num).unwrap();
                            // first visit of this subloop
                            if subloop.parent.is_none() {
                                subloop.parent = Some(cur_loop_num);
                                next = Some(subloop.header);
                            }
                        }
                    }
                }

                if let Some(next) = next
                    && next != header
                {
                    stack
                        .extend(graph.preds(next).filter(|pred| dom_tree.dominates(header, *pred)));
                }
            }
        }

        // thanks to RPO, when we calculate the deps of loop with larger id, it's parent's depth
        // has already been set
        for id in keys {
            if let Some(p) = self.loops[&id].parent {
                let parent_level = self.loops[&p].level;
                self.loops.get_mut(&id).unwrap().level = parent_level + 1;
            } else {
                self.loops.get_mut(&id).unwrap().level = 1; // root loop
            }
        }
    }

    /// add a new bb to a loop, returns if the bb's loop is set by us
    pub fn add_bb_to_loop(&mut self, lp: Loop, node: N) -> bool {
        if let std::collections::hash_map::Entry::Vacant(e) = self.bb_to_loop.entry(node) {
            e.insert(lp);
            true
        } else {
            false
        }
    }

    /// returns if the loop contains a given node
    pub fn contains(&self, lp: Loop, node: N) -> bool {
        let Some(mut target_lp) = self.bb_to_loop.get(&node).copied() else {
            return false;
        };
        while let Some(loop_data) = self.loops.get(&target_lp) {
            if target_lp == lp {
                return true;
            }
            if let Some(parent) = loop_data.parent {
                target_lp = parent;
            } else {
                break;
            }
        }
        false
    }

    /// bottom up, inner -> outer
    pub fn bottom_up(&self) -> impl Iterator<Item = Loop> {
        let mut res = self.loops.iter().map(|(lp, data)| (*lp, data.level)).collect::<Vec<_>>();
        res.sort_by_key(|b| std::cmp::Reverse(b.1));
        res.into_iter().map(|(lp, _)| lp)
    }

    /// reverse `bb_to_loop`
    pub fn loop_to_bb(&self) -> HashMap<Loop, Vec<N>> {
        let mut res: HashMap<Loop, Vec<N>> = HashMap::new();
        for (k, v) in &self.bb_to_loop {
            res.entry(*v).or_default().push(*k);
        }

        res
    }

    /// preheader: BB that is the only pred of the loop header that doesn't belong to the loop
    pub fn preheader<G: DirectedGraph<Node = N> + Graph>(&self, graph: &G, lp: Loop) -> Option<N> {
        let header = self.loops.get(&lp)?.header;
        let mut preheader = None;
        for pred in graph.preds(header).filter(move |&pred| !self.contains(lp, pred)) {
            match preheader {
                None => preheader = Some(pred),
                Some(_) => return None,
            }
        }
        preheader
    }

    /// exits: BB that doesn't belong to the loop but one of its pred does
    pub fn exits<G: DirectedGraph<Node = N> + Graph>(
        &self,
        graph: &G,
        lp: Loop,
    ) -> impl Iterator<Item = N> {
        graph.nodes_iter().filter(move |&node| {
            !self.contains(lp, node) && graph.preds(node).any(|pred| self.contains(lp, pred))
        })
    }

    /// latches: BB that contained by the loop and have on edge to the header of the loop header
    pub fn latches<G: DirectedGraph<Node = N> + Graph>(&self, graph: &G, lp: Loop) -> Vec<N> {
        let Some(data) = self.loops.get(&lp) else {
            return vec![];
        };
        graph.preds(data.header).filter(move |&node| self.contains(lp, node)).collect()
    }

    /// loop header:
    ///     BB that dominates one of its predecessors
    fn is_loop_header<G: DirectedGraph<Node = N> + Graph>(
        graph: &G,
        node: N,
        dom_tree: &DomTree<N>,
    ) -> bool {
        graph.preds(node).any(|pred| dom_tree.dominates(node, pred))
    }
}

#[cfg(test)]
mod tests {
    use petgraph::graph::DiGraph;

    use super::*;
    // Assuming DomTree is in crate::graph::dom_tree
    use crate::graph::dom_tree::DomTree;

    #[test]
    fn test_simple_loop() {
        let mut g = DiGraph::<&str, ()>::new();
        let entry = g.add_node("Entry");
        let header = g.add_node("Header");
        let body = g.add_node("Body");
        let exit = g.add_node("Exit");

        g.add_edge(entry, header, ());
        g.add_edge(header, body, ());
        g.add_edge(body, header, ()); // Backedge
        g.add_edge(header, exit, ());

        let dom_tree = DomTree::build(entry, &g);
        let mut analysis = LoopsAnalysis::new();
        analysis.compute(&g, entry, &dom_tree);

        let loops = analysis.loops();
        let bb_to_loop = analysis.bb_to_loop();

        // 1. Check loop count
        assert_eq!(loops.len(), 1, "There should be exactly 1 loop");

        // 2. Check loop properties
        let loop_0 = loops.get(&Loop(0)).unwrap();
        assert_eq!(loop_0.header, header);
        assert_eq!(loop_0.parent, None, "Top level loop should have no parent");
        assert_eq!(loop_0.level, 1);

        // 3. Check BB mapping
        assert_eq!(bb_to_loop.get(&header), Some(&Loop(0)));
        assert_eq!(bb_to_loop.get(&body), Some(&Loop(0)));
        assert_eq!(bb_to_loop.get(&entry), None, "Entry is not in a loop");
        assert_eq!(bb_to_loop.get(&exit), None, "Exit is not in a loop");
    }

    #[test]
    fn test_nested_loops() {
        let mut g = DiGraph::<&str, ()>::new();
        let entry = g.add_node("Entry");
        let outer_header = g.add_node("OuterHeader");
        let inner_header = g.add_node("InnerHeader");
        let inner_latch = g.add_node("InnerLatch");
        let outer_latch = g.add_node("OuterLatch");

        g.add_edge(entry, outer_header, ());
        g.add_edge(outer_header, inner_header, ());
        g.add_edge(inner_header, inner_latch, ());
        g.add_edge(inner_latch, inner_header, ()); // Inner backedge
        g.add_edge(inner_latch, outer_latch, ());
        g.add_edge(outer_latch, outer_header, ()); // Outer backedge

        let dom_tree = DomTree::build(entry, &g);
        let mut analysis = LoopsAnalysis::new();
        analysis.compute(&g, entry, &dom_tree);

        let loops = analysis.loops();
        let bb_to_loop = analysis.bb_to_loop();

        assert_eq!(loops.len(), 2);

        // Because of Reverse Post Order, the outer loop is typically discovered first (ID 0)
        // and the inner loop is discovered second (ID 1).
        // Let's find IDs dynamically to make the test less fragile.
        let outer_id = loops.iter().find(|(_, data)| data.header == outer_header).unwrap().0;
        let inner_id = loops.iter().find(|(_, data)| data.header == inner_header).unwrap().0;

        // Check Outer Loop properties
        assert_eq!(loops[outer_id].parent, None);
        assert_eq!(loops[outer_id].level, 1);

        // Check Inner Loop properties
        assert_eq!(loops[inner_id].parent, Some(*outer_id));
        assert_eq!(loops[inner_id].level, 2);

        // Check BB mapping (ensure nodes map to the INNERMOST loop)
        assert_eq!(bb_to_loop.get(&outer_header), Some(outer_id));
        assert_eq!(bb_to_loop.get(&outer_latch), Some(outer_id));
        assert_eq!(bb_to_loop.get(&inner_header), Some(inner_id));
        assert_eq!(bb_to_loop.get(&inner_latch), Some(inner_id));
        assert_eq!(bb_to_loop.get(&entry), None);
    }

    #[test]
    fn test_sibling_loops() {
        let mut g = DiGraph::<&str, ()>::new();
        let entry = g.add_node("Entry");
        let header1 = g.add_node("Header1");
        let header2 = g.add_node("Header2");

        g.add_edge(entry, header1, ());
        g.add_edge(header1, header1, ()); // Loop 1 (Self loop)
        g.add_edge(entry, header2, ());
        g.add_edge(header2, header2, ()); // Loop 2 (Self loop)

        let dom_tree = DomTree::build(entry, &g);
        let mut analysis = LoopsAnalysis::new();
        analysis.compute(&g, entry, &dom_tree);

        let loops = analysis.loops();
        assert_eq!(loops.len(), 2);

        // Both loops should be at level 1 with no parents
        for (_, loop_data) in loops.iter() {
            assert_eq!(loop_data.parent, None);
            assert_eq!(loop_data.level, 1);
        }
    }
}
