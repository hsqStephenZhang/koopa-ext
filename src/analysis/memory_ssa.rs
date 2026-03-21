use koopa::ir::{BasicBlock, Value};
use rustc_hash::FxHashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct MemoryVersion(u32);

#[allow(unused)]
pub struct MemorySSA {
    block_params: FxHashMap<BasicBlock, Option<MemoryVersion>>,
    mem_defs: FxHashMap<Value, MemoryVersion>,
    mem_uses: FxHashMap<Value, MemoryVersion>,
}
