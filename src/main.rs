extern crate llvm_sys;
extern crate rand;

pub mod parse;
pub mod codemap;
pub mod mir;
pub mod util;
pub mod llvm;
pub mod compile;

use compile::Compiler;
use std::io::{self, Read};

fn main() {
    let mut source = String::new();
    io::stdin().read_to_string(&mut source).unwrap();
    let mut compiler = Compiler::from_str(&source);
    compiler.compile().unwrap();

    println!("{}", compiler.run());
}
