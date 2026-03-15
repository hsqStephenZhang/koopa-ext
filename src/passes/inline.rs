use koopa::ir::builder::{BasicBlockBuilder, LocalInstBuilder, ValueBuilder};
use koopa::ir::{Function, FunctionData, TypeKind, ValueKind};
use koopa::opt::ModulePass;
use rustc_hash::FxHashMap;

use crate::ext::FunctionDataExt;
use crate::utils::clone_bb;

#[derive(Default)]
pub struct Inliner {
    should_inline: FxHashMap<Function, bool>,
}

impl Inliner {
    pub fn new() -> Self {
        Self::default()
    }
}

impl ModulePass for Inliner {
    fn run_on(&mut self, program: &mut koopa::ir::Program) {
        let funcs = program.funcs().keys().copied().collect::<Vec<_>>();

        for f in funcs {
            let mut bbs = program.func(f).layout().bbs().keys().copied().collect::<Vec<_>>();

            while let Some(bb) = bbs.pop() {
                let insts = program
                    .func(f)
                    .layout()
                    .bbs()
                    .node(&bb)
                    .unwrap()
                    .insts()
                    .iter()
                    .map(|(inst, _)| *inst)
                    .collect::<Vec<_>>();

                for inst in insts {
                    let (target_func, call_args) = match program.func(f).dfg().value(inst).kind() {
                        ValueKind::Call(call) => {
                            if !self.should_inline(call.callee(), program.func(call.callee())) {
                                continue;
                            }
                            (call.callee(), call.args().to_vec())
                        }
                        _ => continue,
                    };

                    let new_entry = program.func(f).layout().entry_bb().unwrap();
                    let ret_ty = program.func(f).dfg().value(inst).ty().clone();

                    let mut vmap = call_args
                        .iter()
                        .copied()
                        .zip(program.func(target_func).params().iter().copied())
                        .collect::<FxHashMap<_, _>>();

                    // 1) split current bb into pre and after parts, add after to bbs for further inline
                    let after_bb_name = program
                        .func(f)
                        .dfg()
                        .bb(bb)
                        .name()
                        .as_deref()
                        .map(|n| format!("{}_after", n));

                    let after_bb_params =
                        if ret_ty.is_unit() { vec![] } else { vec![ret_ty.clone()] };

                    let after_bb = program
                        .func_mut(f)
                        .dfg_mut()
                        .new_bb()
                        .basic_block_with_params(after_bb_name, after_bb_params);

                    program.func_mut(f).layout_mut().bbs_mut().push_key_back(after_bb).unwrap();

                    let mut cursor =
                        program.func_mut(f).layout_mut().bb_mut(bb).insts_mut().cursor_mut(inst);

                    let mut moved = vec![];
                    while let Some(i) = cursor.key() {
                        moved.push(*i);
                        cursor.remove_current();
                    }

                    // `moved[0]` is the call itself. We retain its SSA ID, but redefine it to return
                    // the parameter piped into `after_bb` (add %param, 0).
                    // This way we organically avoid "cloning" usages & gracefully RAUW cross-block uses!
                    if ret_ty.is_i32() {
                        let param = program.func(f).dfg().bb(after_bb).params()[0];
                        let zero = program.func_mut(f).dfg_mut().new_value().integer(0);
                        program.func_mut(f).dfg_mut().replace_value_with(inst).binary(
                            koopa::ir::BinaryOp::Add,
                            param,
                            zero,
                        );
                        program
                            .func_mut(f)
                            .layout_mut()
                            .bb_mut(after_bb)
                            .insts_mut()
                            .push_key_back(inst)
                            .unwrap();
                    } else if matches!(ret_ty.kind(), TypeKind::Pointer(_)) {
                        let param = program.func(f).dfg().bb(after_bb).params()[0];
                        let zero = program.func_mut(f).dfg_mut().new_value().integer(0);
                        program.func_mut(f).dfg_mut().replace_value_with(inst).get_ptr(param, zero);
                        program
                            .func_mut(f)
                            .layout_mut()
                            .bb_mut(after_bb)
                            .insts_mut()
                            .push_key_back(inst)
                            .unwrap();
                    }

                    // For the rest of instructions natively MOVE them (no clone IDs!)
                    // which flawlessly keeps variables in-sync across other branches!
                    for m in moved.into_iter().skip(1) {
                        program
                            .func_mut(f)
                            .layout_mut()
                            .bb_mut(after_bb)
                            .insts_mut()
                            .push_key_back(m)
                            .unwrap();
                    }

                    bbs.push(after_bb);

                    // 2) alloc handling (capture targets across all cloned BBs optimally)
                    let mut target_allocs = vec![];
                    for (_, node) in program.func(target_func).layout().bbs() {
                        for &i in node.insts().keys() {
                            if matches!(
                                program.func(target_func).dfg().value(i).kind(),
                                ValueKind::Alloc(_)
                            ) {
                                target_allocs.push(i);
                            }
                        }
                    }

                    let mut new_allocs = Vec::new();
                    for old_alloc in target_allocs {
                        let ty = program.func(target_func).dfg().value(old_alloc).ty().clone();
                        let elem_ty = match ty.kind() {
                            koopa::ir::TypeKind::Pointer(base) => base.clone(),
                            _ => unreachable!("alloc value must be a pointer"),
                        };
                        let new_alloc = program.func_mut(f).dfg_mut().new_value().alloc(elem_ty);
                        vmap.insert(old_alloc, new_alloc);
                        new_allocs.push(new_alloc);
                    }

                    // place allocs at the front of the caller's entry block
                    let insts_mut = program.func_mut(f).layout_mut().bb_mut(new_entry).insts_mut();
                    for new_alloc in new_allocs.into_iter().rev() {
                        insts_mut.push_key_front(new_alloc).unwrap();
                    }

                    // 3-4) pre-create target entry + other bbs map
                    let old_entry = program.func(target_func).layout().entry_bb().unwrap();
                    let old_bbs = program.func(target_func).all_bbs();
                    let mut bb_map = FxHashMap::default();

                    for &old_bb in &old_bbs {
                        let old_name = program.func(target_func).dfg().bb(old_bb).name().clone();
                        let new_name = old_name.map(|n| format!("{}_clone", n));

                        let new_param_tys = if old_bb == old_entry {
                            program
                                .func(target_func)
                                .params()
                                .iter()
                                .map(|&p| program.func(target_func).dfg().value(p).ty().clone())
                                .collect::<Vec<_>>()
                        } else {
                            program
                                .func(target_func)
                                .dfg()
                                .bb(old_bb)
                                .params()
                                .iter()
                                .map(|&p| program.func(target_func).dfg().value(p).ty().clone())
                                .collect::<Vec<_>>()
                        };

                        let new_bb = program
                            .func_mut(f)
                            .dfg_mut()
                            .new_bb()
                            .basic_block_with_params(new_name, new_param_tys);
                        program.func_mut(f).layout_mut().bbs_mut().push_key_back(new_bb).unwrap();
                        bb_map.insert(old_bb, new_bb);

                        let created_params = program.func(f).dfg().bb(new_bb).params().to_vec();
                        let old_params = if old_bb == old_entry {
                            program.func(target_func).params().to_vec()
                        } else {
                            program.func(target_func).dfg().bb(old_bb).params().to_vec()
                        };

                        for (op, np) in old_params.into_iter().zip(created_params) {
                            vmap.insert(op, np);
                        }
                    }

                    // 5) clone instructions natively into the pre-created blocks (also handling terminators automatically)
                    for &old_bb in &old_bbs {
                        let new_bb = bb_map[&old_bb];
                        clone_bb(
                            program,
                            target_func,
                            f,
                            &mut vmap,
                            &bb_map,
                            old_bb,
                            new_bb,
                            Some(after_bb),
                        );
                    }

                    // finish step 1): replace original `call` site with jump to cloned entry
                    let new_entry_clone = bb_map[&old_entry];

                    let jump_to_inlined = program
                        .func_mut(f)
                        .dfg_mut()
                        .new_value()
                        .jump_with_args(new_entry_clone, call_args);

                    program
                        .func_mut(f)
                        .layout_mut()
                        .bb_mut(bb)
                        .insts_mut()
                        .push_key_back(jump_to_inlined)
                        .unwrap();

                    break;
                }
            }
        }
    }
}

impl Inliner {
    const INST_THRES: usize = 15;

    pub fn should_inline(&mut self, func: Function, data: &FunctionData) -> bool {
        if let Some(res) = self.should_inline.get(&func) {
            *res
        } else {
            let res = Self::should_inline_inner(func, data);
            self.should_inline.insert(func, res);
            res
        }
    }

    /// simple heuristics
    ///     1. the function body is known
    ///     2. instruction count is less than N
    ///     3. has no function call(too conservative)
    fn should_inline_inner(_func: Function, data: &FunctionData) -> bool {
        if data.layout().entry_bb().is_none() {
            return false;
        }

        let inst_cnt = data.inst_count();
        if inst_cnt > Self::INST_THRES {
            return false;
        }

        for (bb, _) in data.layout().bbs() {
            for (&inst, _) in data.layout().bbs().node(bb).unwrap().insts() {
                if matches!(data.dfg().value(inst).kind(), ValueKind::Call(_)) {
                    return false;
                }
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use koopa::back::koopa::Visitor as KoopaVisitor;
    use koopa::back::{NameManager, Visitor};
    use koopa::front::Driver;
    use koopa::opt::FunctionPass;

    use super::*;
    use crate::passes::SimplifyCFG;

    fn apply_pass(ir_text: &str, simplify: bool, debug_on: bool) {
        let driver = Driver::from(ir_text);
        let mut program = driver.generate_program().unwrap();
        let mut pass = Inliner::new();
        pass.run_on(&mut program);
        if simplify {
            let mut pass = SimplifyCFG;
            for (func, data) in program.funcs_mut() {
                pass.run_on(*func, data);
            }
        }

        if debug_on {
            let mut visitor = KoopaVisitor;
            let mut nm = NameManager::new();
            let mut w = std::io::stdout();
            visitor.visit(&mut w, &mut nm, &program).unwrap();
        }
    }

    #[test]
    fn test_simple() {
        let ir = r#"
fun @add(%c1: i32, %c2: i32): i32 {
%entry_add:
  %final = add %c1, %c2
  ret %final
}

fun @sub(%c1: i32, %c2: i32): i32 {
%entry_sub:
  %final = sub %c1, %c2
  ret %final
}

fun @caller_basic(%c1: i32, %c2: i32): i32 {
%entry:
  %res1 = call @add(%c1, %c2)
  %res2 = call @sub(%res1, 1)
  ret %res2
}
        "#;

        apply_pass(ir, true, true);
    }

    #[test]
    fn test_multi_ret() {
        let ir = r#"
fun @callee_multi_ret(%cond: i32, %val: i32): i32 {
%entry:
    %is_zero = eq %val, 0
    br %is_zero, %ret_early, %check_cond

%ret_early:
    ret 0

%check_cond:
    %c = gt %cond, 10
    br %c, %ret_a, %ret_b

%ret_a:
    %res_a = add %val, 1
    ret %res_a

%ret_b:
    %res_b = sub %val, 1
    ret %res_b
}

fun @test_multi_ret(%a: i32, %b: i32): i32 {
%entry:
    %result = call @callee_multi_ret(%a, %b)
    %final = mul %result, 2
    ret %final
}
        "#;
        apply_pass(ir, true, true);
    }

    #[test]
    fn test_alloc() {
        let ir = r#"
fun @foo(): i32 {
%entry:
  %ret = alloc i32
  store 13, %ret
  %0 = load %ret
  %1 = add %0, 29
  ret %1
}

fun @test_alloc(): i32 {
%entry:
    %result = call @foo()
    %final = mul %result, 2
    ret %final
}
        "#;
        apply_pass(ir, true, true);
    }

    #[test]
    fn test_global() {
        let ir = r#"
decl @getint(): i32

decl @getch(): i32

decl @getarray(*i32): i32

decl @putint(i32)

decl @putch(i32)

decl @putarray(i32, *i32)

decl @starttime(): i32

decl @stoptime(): i32

fun @add(@a: i32, @b: i32): i32 {
%entry:
  %a = alloc i32
  store @a, %a
  %b = alloc i32
  store @b, %b
  jump %0

%0:
  %1 = load %a
  %2 = load %b
  %3 = add %1, %2
  ret %3

%4:
  ret 0
}

fun @sub(@a: i32, @b: i32): i32 {
%entry:
  %a = alloc i32
  store @a, %a
  %b = alloc i32
  store @b, %b
  jump %5

%5:
  %6 = load %a
  %7 = load %b
  %8 = sub %6, %7
  ret %8

%9:
  ret 0
}

fun @mul(@a: i32, @b: i32): i32 {
%entry:
  %a = alloc i32
  store @a, %a
  %b = alloc i32
  store @b, %b
  jump %10

%10:
  %11 = load %a
  %12 = load %b
  %13 = mul %11, %12
  ret %13

%14:
  ret 0
}

fun @div(@a: i32, @b: i32): i32 {
%entry:
  %a = alloc i32
  store @a, %a
  %b = alloc i32
  store @b, %b
  jump %15

%15:
  %16 = load %a
  %17 = load %b
  %18 = div %16, %17
  ret %18

%19:
  ret 0
}

fun @main(): i32 {
%entry:
  %20 = call @sub(1, 2)
  %21 = call @div(4, 5)
  %22 = call @mul(3, %21)
  %23 = call @add(%20, %22)
  %x = alloc i32
  store %23, %x
  %24 = ne 0, 0
  %25 = alloc i32
  store %24, %25
  br %24, %and_else, %26

%and_else:
  %27 = load %x
  %28 = call @sub(1, %27)
  %29 = ne %28, 0
  store %29, %25
  jump %26

%26:
  %30 = load %25
  %31 = ne %30, 0
  %32 = alloc i32
  store %31, %32
  br %31, %33, %or_else

%or_else:
  %34 = load %x
  %35 = ne %34, 0
  %36 = alloc i32
  store %35, %36
  br %35, %37, %or_else_0

%or_else_0:
  %38 = call @add(1, 2)
  %39 = gt %38, 10
  %40 = ne 0, %39
  store %40, %36
  jump %37

%37:
  %41 = load %36
  %42 = call @div(%41, 5)
  %43 = call @mul(3, %42)
  %44 = ne 0, %43
  store %44, %32
  jump %33

%33:
  %45 = load %32
  %46 = call @add(1, %45)
  %y = alloc i32
  store %46, %y
  %47 = load %x
  %48 = load %y
  %49 = add %47, %48
  ret %49

%50:
  ret 0
}
        "#;
        apply_pass(ir, true, true);
    }

    #[test]
    fn test_empty() {
        let ir = r#"
fun @f(): i32 {
%entry:
  ret 0

%0:
  ret 0
}

fun @main(): i32 {
%entry:
  %1 = call @f()
  ret %1

%2:
  ret 0
}
        "#;
        apply_pass(ir, true, true);
    }
}
