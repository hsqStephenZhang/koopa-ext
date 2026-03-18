use koopa::ir::{BasicBlock, FunctionData, Value, ValueKind};

use crate::graph::DirectedGraph;

pub trait FunctionDataExt {
    fn get_value_by_name(&self, name: &str) -> Option<Value>;

    fn get_bb_by_name(&self, name: &str) -> Option<BasicBlock>;

    fn inst_count(&self) -> usize;

    fn all_bbs(&self) -> Vec<BasicBlock>;

    fn try_eval_i32(&self, value: Value) -> Option<i32>;

    fn bb_of_arg(&self, arg: Value) -> Option<BasicBlock>;

    fn has(&self, value: Value) -> bool;
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

    fn try_eval_i32(&self, value: Value) -> Option<i32> {
        match self.dfg().values().get(&value)?.kind() {
            ValueKind::Integer(integer) => Some(integer.value()),
            ValueKind::ZeroInit(_) => Some(0),
            _ => None,
        }
    }

    fn bb_of_arg(&self, arg: Value) -> Option<BasicBlock> {
        for bb in self.layout().bbs().keys() {
            for param in self.dfg().bb(*bb).params() {
                if *param == arg {
                    return Some(*bb);
                }
            }
        }
        None
    }

    fn has(&self, value: Value) -> bool {
        self.dfg().values().get(&value).is_some()
    }
}
