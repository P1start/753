//! Coordinates the various passes required to compile a full program.
//! 
//! See src/notes.md for details on how this will work.

use parser::{Parser, Item};
use resolve::{self, Resolution};
use codemap::{FileId, FileInfo};
use util::Error;

use std::fs::File;
use std::path::Path;
use std::io::Read;
use std::collections::HashMap;

pub struct Coordinator {
    pub items: Vec<Item>,
    pub resolutions: Vec<Option<Resolution>>,

    pub globals: HashMap<String, usize>,

    file_info: Vec<FileInfo>,
    next_file_id: u32,
}

impl Coordinator {
    pub fn from_path(path: &Path) -> Result<Coordinator, Error> {
        let mut coordinator = Coordinator {
            items: vec![],
            resolutions: vec![],
            globals: HashMap::new(),
            file_info: vec![],
            next_file_id: 0,
        };

        let mut file = File::open(path)?;

        let mut source = String::new();
        file.read_to_string(&mut source)?;
        let file_info = FileInfo { name: path.to_owned() };
        let mut parser = Parser::from_source(&source, coordinator.new_file_id(file_info));

        let items = parser.parse_items()?;
        for item in items {
            coordinator.items.push(item);
            coordinator.resolutions.push(None);
        }

        Ok(coordinator)
    }

    fn new_file_id(&mut self, file_info: FileInfo) -> FileId {
        let file_id = self.next_file_id;
        self.next_file_id += 1;
        self.file_info.push(file_info);
        FileId(file_id)
    }

    pub fn resolve_names(&mut self) {
        for (i, item) in self.items.iter().enumerate() {
            let name = item.get_base_name();
            self.resolutions[i] = Some(resolve::resolve_names_in_item(&item));
            self.globals.insert(name.to_string(), i);
        }
    }
}