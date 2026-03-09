use koopa::ir::BasicBlock;

pub trait DirectedGraph {
    type Node: Copy + PartialEq + Eq + core::hash::Hash + core::fmt::Debug;

    fn num_nodes(&self) -> usize;
}

impl DirectedGraph for koopa::ir::FunctionData {
    type Node = BasicBlock;

    fn num_nodes(&self) -> usize {
        self.dfg().bbs().len()
    }
}

pub trait Predecessors: DirectedGraph {
    fn preds(&self, cur: Self::Node) -> impl Iterator<Item = Self::Node>;
}

impl Predecessors for koopa::ir::FunctionData {
    fn preds(&self, cur: Self::Node) -> impl Iterator<Item = Self::Node> {
        self.dfg().bb(cur).used_by().into_iter().filter_map(|v| self.layout().parent_bb(*v))
    }
}

pub trait Successors: DirectedGraph {
    fn succs(&self, cur: Self::Node) -> impl Iterator<Item = Self::Node>;
}

impl Successors for koopa::ir::FunctionData {
    fn succs(&self, cur: Self::Node) -> impl Iterator<Item = Self::Node> {
        let mut res: smallvec::SmallVec<[BasicBlock; 2]> = smallvec::SmallVec::new();
        let last_inst = self.layout().bbs().node(&cur).unwrap().insts().back_key().cloned();
        if let Some(inst) = last_inst {
            match self.dfg().value(inst).kind() {
                koopa::ir::ValueKind::Branch(branch) => {
                    res.push(branch.true_bb());
                    res.push(branch.false_bb());
                }
                koopa::ir::ValueKind::Jump(jump) => res.push(jump.target()),
                _ => {}
            }
        }
        res.into_iter()
    }
}

pub trait Graph: Successors + Predecessors {}

impl<T> Graph for T where T: Successors + Predecessors {}

#[cfg(test)]
mod tests {
    use koopa::front::Driver;

    use super::*;

    #[test]
    fn test_preds_succs() {
        let src = r#"
decl @getint(): i32

fun @test(): i32 {
%entry:
  %0 = call @getint()
  %1 = call @getint()
  jump %while_cond_2(0, 0)

%while_cond_2(%2: i32, %3: i32):
  %4 = lt %3, %1
  br %4, %while_body_3, %while_end_1

%while_body_3:
  jump %while_cond_4(%2, 0)

%while_end_1:
  ret %2

%while_cond_4(%5: i32, %6: i32):
  %7 = lt %6, %0
  br %7, %while_body_6, %while_end_5

%while_body_6:
  %8 = add %5, %3
  %9 = add %8, %6
  %10 = add %6, 1
  jump %while_cond_4(%9, %10)

%while_end_5:
  %11 = add %3, 1
  jump %while_cond_2(%5, %11)
}
"#;
        let driver: Driver<_> = src.into();
        let prog = driver.generate_program().unwrap();
        let func = prog.funcs().values().find(|bb| bb.name() == "@test").unwrap();

        println!("predecessors:");
        let bbs = func.layout().bbs();
        for (bb, _) in bbs {
            let name = func.dfg().bb(*bb).name().as_deref();
            let pres = func.preds(*bb).map(|bb| func.dfg().bb(bb).name().as_deref());
            println!("{:?} <- {:?}", name, pres.collect::<Vec<_>>());
        }

        println!("sucesssors:");
        for (bb, _) in bbs {
            let name = func.dfg().bb(*bb).name().as_deref();
            let pres = func.succs(*bb).map(|bb| func.dfg().bb(bb).name().as_deref());
            println!("{:?} -> {:?}", name, pres.collect::<Vec<_>>());
        }
    }
}
