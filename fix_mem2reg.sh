sed -i 's/koopa::alloc::vec!/vec!/g' src/passes/mem2reg.rs
sed -i 's/for &use_val in/for use_val in/g' src/passes/mem2reg.rs
sed -i 's/crate::graph::traverse::reverse_post_order(&\*self.data)/crate::graph::traverse::reverse_post_order(\&*self.data, entry_bb)/g' src/passes/mem2reg.rs
