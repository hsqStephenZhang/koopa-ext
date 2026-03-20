use koopa::back::koopa::Visitor as KoopaVisitor;
use koopa::back::{NameManager, Visitor};
use koopa::opt::ModulePass;

pub struct PrintIR;

impl ModulePass for PrintIR {
    fn run_on(&mut self, program: &mut koopa::ir::Program) {
        let mut visitor = KoopaVisitor;
        let mut nm = NameManager::new();
        let mut w = std::io::stdout();
        visitor.visit(&mut w, &mut nm, &program).unwrap();
    }
}
