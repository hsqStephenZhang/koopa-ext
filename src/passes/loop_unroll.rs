use koopa::ir::builder::{BasicBlockBuilder, LocalInstBuilder, ValueBuilder};
use koopa::ir::{BasicBlock, BinaryOp, ValueKind};
use koopa::opt::FunctionPass;
use rustc_hash::FxHashMap;

use crate::ext::FunctionDataExt;
use crate::graph::dom_tree::DomTree;
use crate::graph::loops::{Loop, LoopsAnalysis};
use crate::graph::scalar_evolution::ScalarEvolutionAnalysis;
use crate::graph::terminator::TerminatorExt;
use crate::graph::traverse::reverse_post_order;
use crate::utils::{clone_bb_in_same_func, replace_operands};

const FULL_UNROLL_CNT: usize = 10;

pub struct LoopUnRoll;

#[derive(Clone, Debug)]
enum UnrollVerdict {
    /// fully unroll, should copy the loop for `cnt-1` times
    /// (base, step, bound)
    Full(i32, i32, i32),
    Not,
}

impl FunctionPass for LoopUnRoll {
    fn run_on(&mut self, _func: koopa::ir::Function, data: &mut koopa::ir::FunctionData) {
        let Some(entry) = data.layout().entry_bb() else {
            return;
        };
        let rpo = reverse_post_order(data, entry);
        let bb_to_rpo_num =
            rpo.into_iter().enumerate().map(|(i, bb)| (bb, i)).collect::<FxHashMap<_, _>>();
        let dom_tree = DomTree::build(entry, data);
        let mut loops = LoopsAnalysis::new();
        loops.compute(data, entry, &dom_tree);

        let mut scev = ScalarEvolutionAnalysis::new();
        scev.compute(data, &loops);

        // start from the inner loop
        for lp in loops.bottom_up() {
            match self.should_unroll(data, lp, &loops, &mut scev) {
                UnrollVerdict::Full(base, step, bound) => {
                    let cnt = (bound - base + step - 1) / step;

                    // clone all the block of the loop for `cnt-1` times
                    // so we will have `cnt` copy of the loop

                    // 1. for the header of the first `cnt-1` copies
                    //    the original `br .., %exit` should be replaced with `jump ..`

                    // 2. for the latch(should only be one after loop canonicalization) of the first `cnt-1` copies
                    //    the original                 `jump %header(%arg1, %arg2)`
                    //    should be replaced with      `jump %next_header(%arg1_step, %arg2_step)`
                    // the step value of each block param should be created via an
                    // instruction at the end of each

                    // clone loops first, then fix the terminators

                    let mut last_bb_map: Option<FxHashMap<BasicBlock, BasicBlock>> = None;

                    let latches = loops.latches(data, lp);
                    assert_eq!(latches.len(), 1);
                    let latch = latches[0];
                    let header = loops.loops()[&lp].header();
                    let exits = loops.exits(data, lp).collect::<Vec<_>>();
                    assert_eq!(exits.len(), 1);
                    let exit = exits[0];

                    let mut loop_bbs = loops.loop_to_bb()[&lp].clone();
                    loop_bbs.sort_by(|a, b| bb_to_rpo_num[a].cmp(&bb_to_rpo_num[b]));

                    // header -> body (no jump to exit)
                    for i in 0..cnt {
                        let mut v_map = FxHashMap::default();

                        // the last unroll should only clone the header
                        // and jump to the exit directly
                        let cloned_bbs = if i + 1 == cnt { &[header] } else { &loop_bbs[..] };
                        let bb_map = cloned_bbs
                            .iter()
                            .map(|old| {
                                let old_bb_data = data.dfg().bb(*old);
                                let name =
                                    old_bb_data.name().as_deref().map(|n| format!("{}_unroll", n));
                                let params = data.bb_params_name_tys(*old);

                                let new_bb = data
                                    .dfg_mut()
                                    .new_bb()
                                    .basic_block_with_param_names(name, params);
                                data.layout_mut().bbs_mut().push_key_back(new_bb).unwrap();
                                (*old, new_bb)
                            })
                            .collect::<FxHashMap<_, _>>();

                        let new_header = bb_map[&header];

                        // v_map must contains all the BB params mappings
                        // to make it work
                        for (&old_bb, &new_bb) in &bb_map {
                            let old_params = data.dfg().bb(old_bb).params();
                            let new_params = data.dfg().bb(new_bb).params();
                            for (old, new) in old_params.into_iter().zip(new_params) {
                                v_map.insert(*old, *new);
                            }
                        }

                        // itherate by RPO to make sure that def is handled before use
                        for old in cloned_bbs.iter() {
                            let new = bb_map[old];
                            clone_bb_in_same_func(data, &mut v_map, &bb_map, *old, new);
                        }

                        // prev_latch -> current_header
                        let prev_latch = last_bb_map.as_ref().map(|m| m[&latch]).unwrap_or(latch);
                        let current_header = bb_map[&header];

                        let (jmp, jmp_data) = data.terminator_raw(prev_latch);
                        let args = match jmp_data.kind() {
                            ValueKind::Jump(jump) => jump.args(),
                            _ => unreachable!(),
                        };
                        data.dfg_mut()
                            .replace_value_with(jmp)
                            .jump_with_args(current_header, args.to_vec());

                        // the original terminator looks like: `br %cond, %next, %exit`
                        //  1. for the first cnt-1 unroll, we need to turn it into `jump %next`
                        //  2. for the last unroll, we need to turn it into `jump %exit`
                        let (br, br_data) = data.terminator_raw(new_header);
                        let (new_target, mut args) = match br_data.kind() {
                            ValueKind::Branch(branch) => {
                                let cond = if i + 1 == cnt {
                                    branch.true_bb() != exit
                                } else {
                                    branch.true_bb() == exit
                                };
                                if cond {
                                    (branch.false_bb(), branch.false_args().to_vec())
                                } else {
                                    (branch.true_bb(), branch.true_args().to_vec())
                                }
                            }
                            _ => unreachable!(),
                        };
                        replace_operands(&mut args, &v_map);
                        data.dfg_mut().replace_value_with(br).jump_with_args(new_target, args);

                        last_bb_map = Some(bb_map);

                        // for all usages of value belongs to the original loop
                        // that's not contained in the loop or unrolled loops
                        // we have to replace them with the latest value
                        if i + 1 == cnt {
                            for inst_or_param in v_map.keys() {
                                for usage in data.dfg().value(*inst_or_param).used_by().clone() {
                                    if let Some(bb) = data.layout().parent_bb(usage)
                                        && !loops.contains(lp, bb)
                                    {
                                        let mut usage_data = data.dfg().value(usage).clone();
                                        replace_operands(&mut usage_data, &v_map);
                                        data.dfg_mut().replace_value_with(usage).raw(usage_data);
                                    }
                                }
                            }
                        }
                    }

                    // original header should also jump to block other than exit
                    let (br, br_data) = data.terminator_raw(header);
                    let (target, args) = match br_data.kind() {
                        ValueKind::Branch(branch) => {
                            if branch.true_bb() == exit {
                                (branch.false_bb(), branch.false_args())
                            } else {
                                (branch.true_bb(), branch.true_args())
                            }
                        }
                        _ => unreachable!(),
                    };
                    data.dfg_mut().replace_value_with(br).jump_with_args(target, args.to_vec());
                }
                UnrollVerdict::Not => {}
            }
        }
    }
}

impl LoopUnRoll {
    fn should_unroll(
        &self,
        data: &koopa::ir::FunctionData,
        lp: Loop,
        loops: &LoopsAnalysis<BasicBlock>,
        scev: &mut ScalarEvolutionAnalysis,
    ) -> UnrollVerdict {
        let bb = loops.loops()[&lp];

        // must be canonical form
        if loops.preheader(data, lp).is_none() {
            return UnrollVerdict::Not;
        }
        if loops.latches(data, lp).len() != 1 {
            return UnrollVerdict::Not;
        }

        let header = bb.header();
        let (_, terminator_data) = data.terminator_raw(header);
        match terminator_data.kind() {
            koopa::ir::ValueKind::Branch(branch) => {
                let cond = branch.cond();
                match data.dfg().value(cond).kind() {
                    ValueKind::Binary(binary) => {
                        let Some(lhs) = scev.get_or_insert(data, loops, lp, binary.lhs()) else {
                            return UnrollVerdict::Not;
                        };
                        let Some(rhs) = scev.get_or_insert(data, loops, lp, binary.rhs()) else {
                            return UnrollVerdict::Not;
                        };

                        // base + i * step < bound
                        if binary.op() == BinaryOp::Lt
                            && let Some(addrec) = lhs.as_addrec()
                            && let Some(base) = addrec.base.as_const()
                            && let Some(step) = addrec.step.as_const()
                            && let Some(c) = rhs.as_const()
                        {
                            let base = base.value();
                            let step = step.value();
                            let bound = c.value();

                            if step <= 0 || base >= bound {
                                return UnrollVerdict::Not;
                            }

                            return if (bound - base + step - 1) / step <= FULL_UNROLL_CNT as i32 {
                                UnrollVerdict::Full(base, step, bound)
                            } else {
                                UnrollVerdict::Not
                            };
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        UnrollVerdict::Not
    }
}

#[cfg(test)]
mod tests {
    use koopa::back::koopa::Visitor as KoopaVisitor;
    use koopa::back::{NameManager, Visitor};
    use koopa::front::Driver;
    use koopa::opt::FunctionPass;

    use crate::passes::loop_unroll::LoopUnRoll;

    fn apply_pass(src: &str, debug_on: bool) {
        let driver: Driver<_> = src.into();
        let mut prog = driver.generate_program().unwrap();
        let (func, data) = prog.funcs_mut().iter_mut().find(|bb| bb.1.name() == "@test").unwrap();
        let mut licm = LoopUnRoll;
        licm.run_on(*func, data);

        if debug_on {
            let mut visitor = KoopaVisitor;
            let mut nm = NameManager::new();
            let mut w = std::io::stdout();
            visitor.visit(&mut w, &mut nm, &prog).unwrap();
        }
    }

    #[test]
    fn test_simple() {
        let ir = r#"
fun @test(): i32 {
%entry:
  jump %cond(0, 0)

%cond(%0: i32, %1: i32):
  %2 = lt %0, 5
  br %2, %body, %dedicate_exit(%1)

%body:
  %5 = add %1, %0
  %6 = add %0, 1
  jump %foo1

%foo1:
  jump %cond(%6, %5)

%foo2(%8: i32):
  ret %8

%dedicate_exit(%10: i32):
  jump %foo2(%10)
}
"#;
        apply_pass(ir, true);
    }

    #[test]
    fn test_arr() {
        let ir = r#"
fun @test(): i32 {
%entry:
  jump %cond(0, 0)

%cond(%0: i32, %1: i32):
  %2 = lt %0, 2
  br %2, %body, %dedicate_exit(%1)

%3(%4: i32):
  jump %5(undef)

%body:
  %6 = eq %0, 1
  br %6, %then, %else

%then:
  %7 = add %1, 1
  jump %8

%8:
  jump %9(%0, %7)

%else:
  %10 = add %1, %0
  jump %9(%0, %10)

%9(%11: i32, %12: i32):
  %13 = add %0, 1
  jump %14

%14:
  jump %cond(%13, %12)

%5(%15: i32):
  ret %15

%16:
  ret 0

%dedicate_exit(%17: i32):
  jump %5(%17)
}
        "#;
        apply_pass(ir, true);
    }

    // #[test]
    // fn
}
