//! Coordinates the various passes required to compile a full program.
//! 
//! See src/notes.md for details on how this will work.

use parser::{Parser, Item, ItemKind, Expr, ExprKind};
use resolve::{self, Resolution};
use codemap::{FileId, FileInfo, Span};
use util::Error;
use mir::{Mir, Context};
use codegen;

use std::fs::File;
use std::path::Path;
use std::io::Read;
use std::collections::{HashMap, HashSet};
use std::mem;

pub struct Coordinator {
    pub items: Vec<Item>,
    pub resolutions: Vec<Option<Resolution>>,

    pub globals: HashMap<String, usize>,

    pub mirs: Vec<Option<Mir>>,

    file_info: Vec<FileInfo>,
    next_file_id: u32,
}

impl Coordinator {
    pub fn from_path(path: &Path) -> Result<Coordinator, Error> {
        let mut coordinator = Coordinator {
            items: vec![],
            resolutions: vec![],
            globals: HashMap::new(),
            mirs: vec![],
            file_info: vec![],
            next_file_id: 0,
        };

        let mut file = File::open(path)?;

        let mut source = String::new();
        file.read_to_string(&mut source)?;
        let file_info = FileInfo { name: path.to_string_lossy().to_string() };
        let mut parser = Parser::from_source(&source, coordinator.new_file_id(file_info));

        let items = parser.parse_items()?;
        for item in items {
            coordinator.items.push(item);
            coordinator.resolutions.push(None);
            coordinator.mirs.push(None);
        }

        Ok(coordinator)
    }

    pub fn from_str(source: &str) -> Result<Self, Error> {
        // FIXME(cleanup): code duplication from from_path
        let mut coordinator = Coordinator {
            items: vec![],
            resolutions: vec![],
            globals: HashMap::new(),
            mirs: vec![],
            file_info: vec![],
            next_file_id: 0,
        };

        let file_info = FileInfo { name: "<string input>".to_string() };
        let mut parser = Parser::from_source(&source, coordinator.new_file_id(file_info));

        let items = parser.parse_items()?;
        for item in items {
            coordinator.items.push(item);
            coordinator.resolutions.push(None);
            coordinator.mirs.push(None);
        }

        Ok(coordinator)
    }

    fn new_file_id(&mut self, file_info: FileInfo) -> FileId {
        let file_id = self.next_file_id;
        self.next_file_id += 1;
        self.file_info.push(file_info);
        FileId(file_id)
    }

    fn resolve_item(&mut self, item_idx: usize) {
        let item = &self.items[item_idx];
        let name = item.get_base_name();
        self.resolutions[item_idx] = Some(resolve::resolve_names_in_item(&item));
        self.globals.insert(name.to_string(), item_idx);
    }

    fn generate_new_function(&mut self, body: Expr) -> usize {
        let item = Item {
            kind: ItemKind::Function(format!("<anon{}>", self.items.len()), body),
            span: Span::dummy(),
        };
        self.items.push(item);
        self.resolutions.push(None);
        self.mirs.push(None);
        self.items.len() - 1
    }

    fn expand(&mut self, item_idx: usize) -> Result<(), Error> {
        // find all (eval)s, generate functions for them and expand & run those functions
        let mut exprs = vec![];
        {
            let item = &mut self.items[item_idx];
            let ItemKind::Function(_, ref mut expr) = item.kind;

            expr.find_toplevel_mut(&mut |e| match e.kind {
                ExprKind::Eval(_) => true,
                _ => false,
            }, &mut |e| {
                // insert a temporary expression so we get ownership of e
                let tmp_expr = Expr {
                    kind: ExprKind::Integer(753),
                    ..*e
                };
                let expr = mem::replace(e, tmp_expr);
                exprs.push(expr);
            });
        }

        for expr in exprs {
            let id = expr.id;
            let inner = match expr.kind {
                ExprKind::Eval(inner) => inner,
                _ => unreachable!(),
            };

            let new_idx = self.generate_new_function(*inner);
            let value = self.compile_and_run(new_idx)?;
            
            let item = &mut self.items[item_idx];
            let ItemKind::Function(_, ref mut expr) = item.kind;
            expr.find_toplevel_mut(
                &mut |e| e.id == id,
                &mut |e| {
                    e.kind = ExprKind::Integer(value);
                },
            )
        }

        Ok(())
    }

    fn expand_and_resolve_dependencies(&mut self, item_idx: usize) -> Result<HashSet<usize>, Error> {
        // FIXME: avoid expanding more than once
        self.expand(item_idx)?;

        if self.resolutions[item_idx].is_none() {
            self.resolve_item(item_idx);
        }

        let dangling_refs = self.resolutions[item_idx].as_ref().unwrap().dangling_refs.clone();
        let mut idxs = HashSet::new();
        idxs.insert(item_idx);
        for item_name in dangling_refs {
            let item_idx = self.items.iter().enumerate().filter(|&(_, item)| (item.get_base_name() == item_name)).map(|(i, _)| i).next().unwrap();
            idxs.insert(item_idx);
            let new_idxs = self.expand_and_resolve_dependencies(item_idx)?;
            idxs.extend(new_idxs);
        }

        Ok(idxs)
    }

    fn compile_and_run(&mut self, item_idx: usize) -> Result<i64, Error> {
        let idxs = self.expand_and_resolve_dependencies(item_idx)?;

        let mut mirs = vec![];
        let mut global_map = HashMap::new();
        for idx in idxs {
            let item = &self.items[idx];
            let context = Context {
                resolution: &self.resolutions[idx].as_ref().unwrap(),
                item,
                globals: &self.globals,
            };
            let mir = Mir::from_context(&context)?;
            global_map.insert(idx, mirs.len());
            mirs.push(mir);
        }
        Ok(codegen::jit_run(&mirs, global_map[&item_idx], global_map))
    }

    pub fn run(&mut self) -> i64 {
        let main_idx = self.items.iter().enumerate().filter(|&(_, x)| x.get_base_name() == "main").map(|(i, _)| i).next().unwrap();
        self.compile_and_run(main_idx).unwrap()
    }
}