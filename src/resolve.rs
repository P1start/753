use std::collections::{HashMap, HashSet};
use parser::{Item, ItemKind, Expr, ExprKind};

/// An identifier for a local binding within a function.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ResolveId(u32);

/// See `Resolution` docs for details about some of this struct's fields.
#[derive(Debug)]
struct Resolver<'ast> {
    lookup: HashMap<*const str, ResolveId>,
    dangling_refs: HashSet<&'ast str>,

    locals: HashMap<&'ast str, ResolveId>,

    item: &'ast Item,

    next_resolve_id: u32,
}

impl<'ast> Resolver<'ast> {
    fn from_item(item: &'ast Item) -> Self {
        let mut resolver = Resolver {
            lookup: HashMap::new(),
            dangling_refs: HashSet::new(),
            locals: HashMap::new(),
            item: &item,
            next_resolve_id: 0,
        };
        resolver.build_lookup_table();
        resolver
    }

    fn generate_new_resolve_id(&mut self) -> ResolveId {
        let old_id = self.next_resolve_id;
        self.next_resolve_id += 1;
        ResolveId(old_id)
    }

    fn build_lookup_table(&mut self) {
        match self.item.kind {
            ItemKind::Function(_, ref body) => {
                self.build_lookup_table_for_expr(body)
            },
        }
    }

    fn build_lookup_table_for_expr(&mut self, expr: &'ast Expr) {
        match expr.kind {
            ExprKind::SExpr(ref exprs) => {
                for expr in exprs {
                    self.build_lookup_table_for_expr(expr);
                }
            },
            ExprKind::Integer(_) => {},
            ExprKind::Ident(ref name) => {
                if let Some(&id) = self.locals.get(&**name) {
                    self.lookup.insert(&**name, id);
                } else {
                    self.dangling_refs.insert(&**name);
                }
            },
            ExprKind::Let(ref name, ref value, ref rest) => {
                self.build_lookup_table_for_expr(value);

                let id = self.generate_new_resolve_id();
                let old_value = self.locals.get(&**name).map(|x| *x);
                self.lookup.insert(&**name, id);
                self.locals.insert(&**name, id);

                self.build_lookup_table_for_expr(rest);

                old_value.map(|old_id| self.locals.insert(&**name, old_id));
            },
        }
    }
}

/// The result of a call to `resolve_names_in_item`.
/// 
/// This contains information about all the local references within an item, as well as any
/// dangling references (probably referring to globals).
#[derive(Debug)]
pub struct Resolution<'ast> {
    /// The lookup table that maps strings from the `ItemKind` to resolve IDs.
    /// 
    /// Lookup is done based on memory address; think of the `*const str` as being an arbitrary
    /// unique ID assigned to every identifier in the `ItemKind`.
    pub lookup: HashMap<*const str, ResolveId>,
    /// All the bindings within the `ItemKind` that don't reference a local variable. This is either
    /// because they reference global variables (which will be resolved later) or they reference
    /// an undefined identifier (in which case the program is invalid).
    pub dangling_refs: HashSet<&'ast str>,
}

pub fn resolve_names_in_item(item: &Item) -> Resolution {
    let resolver = Resolver::from_item(item);
    Resolution {
        lookup: resolver.lookup,
        dangling_refs: resolver.dangling_refs,
    }
}

#[cfg(test)]
mod test {
    #![allow(unused_variables, unreachable_patterns)]
    use super::*;
    use parser::{Parser, ItemKind, ExprKind};

    #[test]
    fn test_basic_name_resolution() {
        let src = "(defun foo (let [a 1] (a b)))";
        let mut parser = Parser::from_source(src);
        let item = parser.parse_item().unwrap();
        let (a1, a2) = match item.kind {
            ItemKind::Function(_, ref expr) => match expr.kind {
                ExprKind::Let(ref a1, _, ref expr) => match expr.kind {
                    ExprKind::SExpr(ref exprs) => match exprs[0].kind {
                        ExprKind::Ident(ref a2) => (&**a1 as *const _, &**a2 as *const _),
                        _ => panic!(),
                    },
                    _ => panic!(),
                },
                _ => panic!(),
            },
        };
        let resolution = resolve_names_in_item(&item);
        let mut expected_dangling_refs = HashSet::new();
        expected_dangling_refs.insert("b");
        assert_eq!(resolution.dangling_refs, expected_dangling_refs);

        let mut expected_lookup = HashMap::new();
        expected_lookup.insert(a1, ResolveId(0));
        expected_lookup.insert(a2, ResolveId(0));
        assert_eq!(resolution.lookup, expected_lookup);
    }
}