use koopa::ir::{BasicBlock, FunctionData, Value};

use crate::graph::DirectedGraph;

pub trait FunctionDataExt {
    fn get_value_by_name(&self, name: &str) -> Option<Value>;

    fn get_bb_by_name(&self, name: &str) -> Option<BasicBlock>;

    fn inst_count(&self) -> usize;

    fn all_bbs(&self) -> Vec<BasicBlock>; 
}

impl FunctionDataExt for FunctionData {
    fn get_value_by_name(&self, name: &str) -> Option<Value> {
        self.dfg().values().iter().find(|(_, v)| v.name().as_deref() == Some(name)).map(|(k, _)| *k)
    }

    fn get_bb_by_name(&self, name: &str) -> Option<BasicBlock> {
        self.dfg().bbs().iter().find(|(_, v)| v.name().as_deref() == Some(name)).map(|(k, _)| *k)
    }

    fn inst_count(&self) -> usize {
        let mut cnt = 0;

        for (bb, _) in self.layout().bbs() {
            cnt += self.layout().bbs().node(bb).unwrap().insts().len();
        }

        cnt
    }
    
    fn all_bbs(&self) -> Vec<BasicBlock> {
        self.nodes_iter().collect()
    }
}
