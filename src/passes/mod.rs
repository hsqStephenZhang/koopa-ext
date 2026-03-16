pub mod dce;
pub mod gvn;
pub mod inline;
pub mod licm;
pub mod loop_unroll;
pub mod simplify_cfg;
pub mod simplify_loop;

pub use dce::DeadCodeElimination;
pub use gvn::GVN;
pub use inline::Inliner;
pub use licm::LICM;
pub use simplify_cfg::SimplifyCFG;
pub use simplify_loop::LoopSimplify;
