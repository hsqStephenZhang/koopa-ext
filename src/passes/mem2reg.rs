use koopa::ir::builder::{LocalInstBuilder, ValueBuilder};
use koopa::ir::{BasicBlock, FunctionData, Type, Value, ValueKind};
use koopa::opt::FunctionPass;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};

use crate::ext::FunctionDataExt;
use crate::graph::{Predecessors, Successors};

pub struct Mem2reg;

impl FunctionPass for Mem2reg {
    fn run_on(&mut self, _func: koopa::ir::Function, data: &mut FunctionData) {
        let mut ssa = SSAConstructor::new(data);
        ssa.run();
    }
}

struct SSAConstructor<'a> {
    data: &'a mut FunctionData,
    var_defs: FxHashMap<(BasicBlock, Value), Value>,
    incomplete_phis: FxHashMap<BasicBlock, FxHashMap<Value, Value>>,
    sealed_blocks: FxHashSet<BasicBlock>,
    preds: FxHashMap<BasicBlock, SmallVec<[BasicBlock; 2]>>,
    succs: FxHashMap<BasicBlock, SmallVec<[BasicBlock; 2]>>,
    var_types: FxHashMap<Value, Type>,
    phi_operands: FxHashMap<Value, Vec<(BasicBlock, Value)>>,
    phi_vars: FxHashMap<Value, Value>,
    phi_block: FxHashMap<Value, BasicBlock>,

    // 修复点：记录每个 Block 中存活的 (变量, 假Phi)
    bb_phi_vars: FxHashMap<BasicBlock, Vec<(Value, Value)>>,
    // 修复点：手动维护假 Phi 的 Use-Def 链，Koopa IR 看不到未插入的 Undef
    phi_users: FxHashMap<Value, FxHashSet<Value>>,
    // 修复点：记录被消除的假 Phi 指向的最终值（类似并查集）
    replaced_phis: FxHashMap<Value, Value>,
}

impl<'a> SSAConstructor<'a> {
    fn new(data: &'a mut FunctionData) -> Self {
        Self {
            data,
            var_defs: Default::default(),
            incomplete_phis: Default::default(),
            sealed_blocks: Default::default(),
            preds: Default::default(),
            succs: Default::default(),
            var_types: Default::default(),
            phi_operands: Default::default(),
            phi_vars: Default::default(),
            phi_block: Default::default(),
            bb_phi_vars: Default::default(),
            phi_users: Default::default(),
            replaced_phis: Default::default(),
        }
    }

    fn run(&mut self) {
        let Some(entry_bb) = self.data.layout().entry_bb() else {
            return;
        };

        // 1. 寻找可提升的 Alloc
        let mut promotable = FxHashSet::default();
        for inst in self.data.insts(entry_bb) {
            if let ValueKind::Alloc(_) = self.data.dfg().value(inst).kind() {
                let mut ok = true;
                for use_val in self.data.dfg().value(inst).used_by().clone() {
                    match self.data.dfg().value(use_val).kind() {
                        ValueKind::Load(l) if l.src() == inst => {}
                        ValueKind::Store(s) if s.dest() == inst => {}
                        _ => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    promotable.insert(inst);
                    let ptr_ty = self.data.dfg().value(inst).ty().clone();
                    if let koopa::ir::TypeKind::Pointer(base) = ptr_ty.kind() {
                        self.var_types.insert(inst, base.clone());
                    } else {
                        unreachable!()
                    }
                }
            }
        }

        if promotable.is_empty() {
            return;
        }

        // 2. 计算 CFG
        for &bb in self.data.layout().bbs().keys() {
            self.succs.entry(bb).or_default().extend(self.data.succs(bb));
            self.preds.entry(bb).or_default().extend(self.data.preds(bb));
        }

        let blocks = crate::graph::traverse::reverse_post_order(&*self.data, entry_bb);
        let mut visited = FxHashSet::default();

        // 3. 为入口赋予初值 Undef
        for &var in &promotable {
            let ty = self.var_types[&var].clone();
            let undef = self.data.dfg_mut().new_value().undef(ty);
            self.write_variable(var, entry_bb, undef);
        }

        let mut loads_to_replace = Vec::new();
        let mut stores_to_remove = Vec::new();

        // 4. 遍历处理 Basic Blocks
        for block in blocks {
            if !self.sealed_blocks.contains(&block) {
                let preds = self.preds.get(&block).map(|v| v.as_slice()).unwrap_or_default();
                if preds.iter().all(|p| visited.contains(p)) {
                    self.seal_block(block);
                }
            }

            for inst in self.data.insts(block) {
                let kind = self.data.dfg().value(inst).kind().clone();
                match kind {
                    ValueKind::Store(s) => {
                        if promotable.contains(&s.dest()) {
                            self.write_variable(s.dest(), block, s.value());
                            stores_to_remove.push((block, inst));
                        }
                    }
                    ValueKind::Load(l) => {
                        if promotable.contains(&l.src()) {
                            let val = self.read_variable(l.src(), block);
                            loads_to_replace.push((block, inst, val));
                        }
                    }
                    _ => {}
                }
            }

            visited.insert(block);

            for succ in self.succs.get(&block).unwrap_or(&smallvec![]).clone() {
                if !self.sealed_blocks.contains(&succ) {
                    let p = self.preds.get(&succ).unwrap();
                    if p.iter().all(|x| visited.contains(x)) {
                        self.seal_block(succ);
                    }
                }
            }
        }

        for bb in self.data.bbs_owned() {
            if !self.sealed_blocks.contains(&bb) {
                self.seal_block(bb);
            }
        }

        // 5. 实例化真正的 Block Parameters (Phi)
        let fake_to_real_phi = self.rebuild_bb_params();
        self.rebuild_terminators(&fake_to_real_phi);

        // 6. 替换所有的 Loads
        for (block, load, val) in loads_to_replace {
            let real_val = self.final_resolve(val, &fake_to_real_phi);
            self.data.replace_all_uses_with(load, real_val);
            self.data.layout_mut().bb_mut(block).insts_mut().remove(&load);
            crate::utils::safely_remove_inst_from_dfg(self.data.dfg_mut(), load);
        }

        // 7. 清理 Stores 和 Allocs
        for (block, store) in stores_to_remove {
            self.data.layout_mut().bb_mut(block).insts_mut().remove(&store);
            crate::utils::safely_remove_inst_from_dfg(self.data.dfg_mut(), store);
        }

        for alloc in promotable {
            self.data.layout_mut().bb_mut(entry_bb).insts_mut().remove(&alloc);
            crate::utils::safely_remove_inst_from_dfg(self.data.dfg_mut(), alloc);
        }
    }

    fn resolve(&self, mut val: Value) -> Value {
        while let Some(&replacement) = self.replaced_phis.get(&val) {
            val = replacement;
        }
        val
    }

    // 修复点：获取最终真正的 Value (转换为 Real Phi)
    fn final_resolve(&self, val: Value, fake_to_real: &FxHashMap<Value, Value>) -> Value {
        let resolved_fake = self.resolve(val);
        *fake_to_real.get(&resolved_fake).unwrap_or(&resolved_fake)
    }

    fn write_variable(&mut self, variable: Value, block: BasicBlock, value: Value) {
        self.var_defs.insert((block, variable), value);
    }

    fn read_variable(&mut self, variable: Value, block: BasicBlock) -> Value {
        if let Some(&val) = self.var_defs.get(&(block, variable)) {
            return self.resolve(val);
        }
        self.read_variable_from_predecessors(variable, block)
    }

    fn read_variable_from_predecessors(&mut self, variable: Value, block: BasicBlock) -> Value {
        let val = if !self.sealed_blocks.contains(&block) {
            let phi = self.new_phi(block, variable);
            self.incomplete_phis.entry(block).or_default().insert(variable, phi);
            phi
        } else {
            let preds = self.preds.get(&block).map(|v| v.as_slice()).unwrap_or_default();
            if preds.len() == 1 {
                self.read_variable(variable, preds[0])
            } else if preds.is_empty() {
                let ty = self.var_types[&variable].clone();
                self.data.dfg_mut().new_value().undef(ty)
            } else {
                let phi = self.new_phi(block, variable);
                self.write_variable(variable, block, phi);
                self.add_phi_operands(block, variable, phi)
            }
        };
        self.write_variable(variable, block, val);
        val
    }

    fn new_phi(&mut self, block: BasicBlock, variable: Value) -> Value {
        let ty = self.var_types[&variable].clone();
        let phi = self.data.dfg_mut().new_value().undef(ty);
        self.bb_phi_vars.entry(block).or_default().push((variable, phi));
        self.phi_vars.insert(phi, variable);
        self.phi_block.insert(phi, block);
        phi
    }

    fn add_phi_operands(&mut self, block: BasicBlock, variable: Value, phi: Value) -> Value {
        let preds = self.preds.get(&block).map(|v| v.as_slice()).unwrap_or_default().to_vec();
        let mut operands = Vec::new();
        for pred in preds {
            let val = self.read_variable(variable, pred);
            operands.push((pred, val));
            // 修复点：记录谁被这个 Phi 使用了
            self.phi_users.entry(val).or_default().insert(phi);
        }
        self.phi_operands.insert(phi, operands);
        self.try_remove_trivial_phi(phi)
    }

    fn seal_block(&mut self, block: BasicBlock) {
        self.sealed_blocks.insert(block);
        if let Some(phis) = self.incomplete_phis.remove(&block) {
            for (variable, phi) in phis {
                self.add_phi_operands(block, variable, phi);
            }
        }
    }

    fn try_remove_trivial_phi(&mut self, phi: Value) -> Value {
        let ops = self.phi_operands.get(&phi).cloned().unwrap_or_default();
        let mut same: Option<Value> = None;
        for &(_, mut op) in &ops {
            op = self.resolve(op); // 确保读取最新的值
            if op == phi || Some(op) == same {
                continue;
            }
            if same.is_some() {
                return phi; // 不平凡
            }
            same = Some(op);
        }

        let same_val = same.unwrap_or_else(|| {
            let var = self.phi_vars[&phi];
            let ty = self.var_types[&var].clone();
            self.data.dfg_mut().new_value().undef(ty)
        });

        // 修复点：在并查集中记录替换路径
        let old = self.replaced_phis.insert(phi, same_val);

        // 修复点：清理 bb_phi_vars，防止生成僵尸参数
        if let Some(block) = self.phi_block.get(&phi).copied() {
            if let Some(vars) = self.bb_phi_vars.get_mut(&block) {
                vars.retain(|&(_, p)| p != phi);
            }
        }

        if old != Some(same_val) {
            // 递归检查它的使用者是否因此变得平凡
            let users = self.phi_users.get(&phi).cloned().unwrap_or_default();
            for u in users {
                if u != phi {
                    self.try_remove_trivial_phi(u);
                }
            }
        }

        same_val
    }

    fn rebuild_bb_params(&mut self) -> FxHashMap<Value, Value> {
        let mut fake_to_real = FxHashMap::default();
        for (&bb, variables) in &self.bb_phi_vars {
            for &(var, fake_phi) in variables {
                let ty = self.var_types[&var].clone();
                let actual_phi = self.data.dfg_mut().append_bb_param(bb, ty);
                fake_to_real.insert(fake_phi, actual_phi);
            }
        }
        fake_to_real
    }

    fn rebuild_terminators(&mut self, fake_to_real: &FxHashMap<Value, Value>) {
        let blocks = self.data.layout().bbs().keys().copied().collect::<Vec<_>>();

        for src in blocks {
            let term = self.data.layout().bbs().node(&src).unwrap().insts().back_key().copied();
            if let Some(term) = term {
                let kind = self.data.dfg().value(term).kind().clone();
                match kind {
                    ValueKind::Jump(j) => {
                        let succ = j.target();
                        let vars = self.bb_phi_vars.get(&succ).cloned().unwrap_or_default();
                        if !vars.is_empty() {
                            let mut args = j.args().to_vec();
                            for (var, _) in vars {
                                let val = self.read_variable(var, src);
                                args.push(self.final_resolve(val, fake_to_real));
                            }
                            self.data.dfg_mut().replace_value_with(term).jump_with_args(succ, args);
                        }
                    }
                    ValueKind::Branch(b) => {
                        let t_vars =
                            self.bb_phi_vars.get(&b.true_bb()).cloned().unwrap_or_default();
                        let f_vars =
                            self.bb_phi_vars.get(&b.false_bb()).cloned().unwrap_or_default();
                        if !t_vars.is_empty() || !f_vars.is_empty() {
                            let mut t_args = b.true_args().to_vec();
                            for (var, _) in t_vars {
                                let val = self.read_variable(var, src);
                                t_args.push(self.final_resolve(val, fake_to_real));
                            }
                            let mut f_args = b.false_args().to_vec();
                            for (var, _) in f_vars {
                                let val = self.read_variable(var, src);
                                f_args.push(self.final_resolve(val, fake_to_real));
                            }
                            self.data.dfg_mut().replace_value_with(term).branch_with_args(
                                b.cond(),
                                b.true_bb(),
                                b.false_bb(),
                                t_args,
                                f_args,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use koopa::back::koopa::Visitor as KoopaVisitor;
    use koopa::back::{NameManager, Visitor};
    use koopa::front::Driver;

    use super::*;

    fn apply_pass(ir_text: &str, debug_on: bool) {
        let driver = Driver::from(ir_text);
        let mut program = driver.generate_program().unwrap();
        let func_id = *program.funcs().keys().next().unwrap();
        let func_data = program.func_mut(func_id);
        let mut pass = Mem2reg;
        pass.run_on(func_id, func_data);

        if debug_on {
            let mut visitor = KoopaVisitor;
            let mut nm = NameManager::new();
            let mut w = std::io::stdout();
            visitor.visit(&mut w, &mut nm, &program).unwrap();
        }
    }

    #[test]
    fn test_mem2reg_basic() {
        let ir = r#"
fun @main(): i32 {
%entry:
    %a = alloc i32
    store 10, %a
    %v = load %a
    ret %v
}
"#;
        apply_pass(ir, true);
    }

    #[test]
    fn test_mem2reg_branch() {
        let ir = r#"
fun @main(%cond: i32): i32 {
%entry:
    %a = alloc i32
    store 10, %a
    br %cond, %then, %else

%then:
    store 20, %a
    jump %end

%else:
    store 30, %a
    jump %end

%end:
    %v = load %a
    ret %v
}
"#;
        apply_pass(ir, true);
    }

    #[test]
    fn test_mem2reg_loop() {
        let ir = r#"
fun @main(): i32 {
%entry:
    %i = alloc i32
    store 0, %i
    jump %cond

%cond:
    %v = load %i
    %c = lt %v, 10
    br %c, %body, %end

%body:
    %v2 = load %i
    %inc = add %v2, 1
    store %inc, %i
    jump %cond

%end:
    %res = load %i
    ret %res
}
"#;
        apply_pass(ir, true);
    }
}
