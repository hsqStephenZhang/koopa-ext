use koopa::ir::builder::{BasicBlockBuilder, LocalInstBuilder, ValueBuilder};
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
    bb_phi_vars: FxHashMap<BasicBlock, Vec<Value>>,
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
        }
    }

    fn run(&mut self) {
        let Some(entry_bb) = self.data.layout().entry_bb() else {
            return;
        };

        // 1. Identify promotable allocs
        let mut promotable = FxHashSet::default();
        for inst in self.data.insts(entry_bb) {
            // check if all usages of alloc are load & store
            // GEP is not supported for now
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

        // 2. Compute CFG for later usage
        for &bb in self.data.layout().bbs().keys() {
            self.succs.entry(bb).or_default().extend(self.data.succs(bb));
            self.preds.entry(bb).or_default().extend(self.data.preds(bb));
        }

        let blocks = crate::graph::traverse::reverse_post_order(&*self.data, entry_bb);
        let mut visited = FxHashSet::default();

        // 3. Init Undef for Promotable
        for &var in &promotable {
            let ty = self.var_types[&var].clone();
            let undef = self.data.dfg_mut().new_value().undef(ty);
            self.write_variable(var, entry_bb, undef);
        }

        let mut loads_to_replace = Vec::new();
        let mut stores_to_remove = Vec::new();

        // 4. Trace blocks
        for block in blocks {
            // Check if we can seal this block before processing
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

            // Forward sealing check: after processing, any successors where all preds are visited can be sealed
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

        for (block, load, val) in loads_to_replace {
            self.data.replace_all_uses_with(load, val);
            self.data.layout_mut().bb_mut(block).insts_mut().remove(&load);
            crate::utils::safely_remove_inst_from_dfg(self.data.dfg_mut(), load);
        }

        for (block, store) in stores_to_remove {
            self.data.layout_mut().bb_mut(block).insts_mut().remove(&store);
            crate::utils::safely_remove_inst_from_dfg(self.data.dfg_mut(), store);
        }

        self.rebuild_terminators();

        for alloc in promotable {
            self.data.layout_mut().bb_mut(entry_bb).insts_mut().remove(&alloc);
            crate::utils::safely_remove_inst_from_dfg(self.data.dfg_mut(), alloc);
        }
    }

    fn write_variable(&mut self, variable: Value, block: BasicBlock, value: Value) {
        self.var_defs.insert((block, variable), value);
    }

    fn read_variable(&mut self, variable: Value, block: BasicBlock) -> Value {
        if let Some(&val) = self.var_defs.get(&(block, variable)) {
            return val;
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

    // TODO: implement it in another way
    fn new_phi(&mut self, block: BasicBlock, variable: Value) -> Value {
        let len = self.data.dfg().bb(block).params().len() + 1;
        let ty = self.var_types[&variable].clone();

        // we have to create params with such length because
        // user might get BlockArgRef's index from it
        let mut dummy_params = vec![koopa::ir::Type::get_i32(); len];
        dummy_params.push(ty);
        let dummy = self.data.dfg_mut().new_bb().basic_block_with_params(None, dummy_params);
        let my_arg = self.data.dfg_mut().bb_mut(dummy).params_mut().pop().unwrap();
        // Just leave the dummy block in layout disconnected, or explicitly drop it
        // We'll leave it without layout, which means it will be filtered out by IR builder.
        // But to be clean we just remove it from DFG
        self.data.dfg_mut().remove_bb(dummy);

        self.data.dfg_mut().bb_mut(block).params_mut().push(my_arg);
        self.bb_phi_vars.entry(block).or_default().push(variable);
        self.phi_vars.insert(my_arg, variable);
        self.phi_block.insert(my_arg, block);
        my_arg
    }

    fn add_phi_operands(&mut self, block: BasicBlock, variable: Value, phi: Value) -> Value {
        let preds = self.preds.get(&block).map(|v| v.as_slice()).unwrap_or_default().to_vec();
        let mut operands = Vec::new();
        for pred in preds {
            let val = self.read_variable(variable, pred);
            operands.push((pred, val));
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
        for &(_, op) in &ops {
            if op == phi || Some(op) == same {
                continue;
            }
            if same.is_some() {
                return phi; // not trivial
            }
            same = Some(op);
        }

        let same_val = same.unwrap_or_else(|| {
            let var = self.phi_vars[&phi];
            let ty = self.var_types[&var].clone();
            self.data.dfg_mut().new_value().undef(ty)
        });

        // Resolve phi manually
        // We can't actually remove block parameters due to index shifts
        // but we replace all its known uses.
        self.data.replace_all_uses_with(phi, same_val);

        // Update var_defs dict
        let mut to_update = Vec::new();
        for (k, v) in &self.var_defs {
            if *v == phi {
                to_update.push(*k);
            }
        }
        for k in to_update {
            self.var_defs.insert(k, same_val);
        }

        // Update phi_operands locally
        for (_, vals) in self.phi_operands.iter_mut() {
            for v in vals.iter_mut() {
                if v.1 == phi {
                    v.1 = same_val;
                }
            }
        }

        // Recursively remove
        // Wait, what if someone uses this phi?
        let users: Vec<_> = self
            .data
            .dfg()
            .value(phi)
            .used_by()
            .iter()
            .filter(|&&u| self.phi_operands.contains_key(&u))
            .copied()
            .collect();

        for u in users {
            self.try_remove_trivial_phi(u);
        }

        same_val
    }

    fn rebuild_terminators(&mut self) {
        let blocks = self.data.layout().bbs().keys().copied().collect::<Vec<_>>();
        for src in blocks {
            let term = self.data.layout().bbs().node(&src).unwrap().insts().back_key().copied();
            if let Some(term) = term {
                let kind = self.data.dfg().value(term).kind().clone();
                match kind {
                    ValueKind::Jump(j) => {
                        let succ = j.target();
                        let mut args = j.args().to_vec();
                        let vars = self.bb_phi_vars.get(&succ).cloned().unwrap_or_default();
                        for var in vars {
                            args.push(self.read_variable(var, src));
                        }
                        self.data.dfg_mut().replace_value_with(term).jump_with_args(succ, args);
                    }
                    ValueKind::Branch(b) => {
                        let mut t_args = b.true_args().to_vec();
                        let t_vars =
                            self.bb_phi_vars.get(&b.true_bb()).cloned().unwrap_or_default();
                        for var in t_vars {
                            t_args.push(self.read_variable(var, src));
                        }
                        let mut f_args = b.false_args().to_vec();
                        let f_vars =
                            self.bb_phi_vars.get(&b.false_bb()).cloned().unwrap_or_default();
                        for var in f_vars {
                            f_args.push(self.read_variable(var, src));
                        }
                        self.data.dfg_mut().replace_value_with(term).branch_with_args(
                            b.cond(),
                            b.true_bb(),
                            b.false_bb(),
                            t_args,
                            f_args,
                        );
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
