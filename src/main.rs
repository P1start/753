extern crate llvm_sys;

pub mod parser;
pub mod resolve;
pub mod codemap;
pub mod coordinate;
pub mod mir;
pub mod util;
pub mod llvm;
pub mod codegen;

use coordinate::Coordinator;
use std::path::Path;

fn main() {
    let mut coordinator = Coordinator::from_path(Path::new("/dev/tty")).unwrap();
    println!("{}", coordinator.run());
}
