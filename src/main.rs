pub mod parser;
pub mod resolve;
pub mod codemap;
pub mod coordinate;
pub mod mir;
pub mod util;

use coordinate::Coordinator;
use std::path::Path;

fn main() {
    let mut coordinator = Coordinator::from_path(Path::new("/dev/tty")).unwrap();
    coordinator.resolve_names();
    coordinator.build_mirs().unwrap();
    for mir in &coordinator.mirs {
        println!("{}", mir.as_ref().unwrap());
    }
}
