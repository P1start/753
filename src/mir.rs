use resolve::{Resolution, ResolveId};
use parser::{Item, ItemKind, Expr, ExprKind};

use std::collections::HashMap;
use std::fmt;

#[derive(Debug)]
pub struct Context<'a> {
    pub resolution: &'a Resolution,
    pub item: &'a Item,
    pub globals: &'a HashMap<String, usize>,
}

#[derive(Debug)]
pub struct Mir {
    pub bbs: Vec<BasicBlock>,
    pub name: String,
    pub variable_info: Vec<VariableInfo>,
}

#[derive(Debug)]
pub struct VariableInfo {
    /// Indicates whether or not the variable is mutable.
    /// 
    /// For example, all temporary variables are immutable.
    pub mutable: bool,
}

impl fmt::Display for Mir {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        for (i, bb) in self.bbs.iter().enumerate() {
            if !first {
                write!(f, "\n")?;
            }
            first = false;
            write!(f, "(bb {} {})", i, bb)?;
        }
        Ok(())
    }
}

impl Mir {
    pub fn from_context(ctxt: &Context) -> Result<Mir, MirError> {
        let mut builder = MirBuilder::from_context(ctxt);
        builder.generate_code()?;
        Ok(Mir {
            bbs: builder.bbs,
            name: ctxt.item.get_base_name().to_string(),
            variable_info: builder.variable_info,
        })
    }
}

#[derive(Debug)]
pub struct BasicBlock {
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

impl fmt::Display for BasicBlock {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "(do")?;
        for instruction in &self.instructions {
            writeln!(f, "    {}", instruction)?;
        }
        writeln!(f, "    {}", self.terminator)?;
        write!(f, ")")
    }
}

impl BasicBlock {
    fn new() -> BasicBlock {
        BasicBlock {
            instructions: vec![],
            terminator: Terminator::Dummy,
        }
    }
}

/// The unique identifier for a variable within this function, including temporary variables.
/// 
/// For local variables with names, this coincides with the identifier generated by resolve.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct VarId(pub u32);

impl fmt::Display for VarId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "var{}", self.0)
    }
}

#[derive(Debug)]
pub enum Instruction {
    /// `var(.0) = .1`
    Assign(VarId, RValue),
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Instruction::Assign(id, ref rvalue) => {
                write!(f, "(set! var{} {})", id.0, rvalue)
            },
        }
    }
}

#[derive(Debug)]
pub enum RValue {
    /// `var(.0)`
    Variable(VarId),
    /// `global(.1)`
    Global(usize),
    /// A constant
    Constant(Value),
    /// `(call var(.0) [var(.1)...])`
    Call(VarId, Vec<VarId>),
}

impl fmt::Display for RValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            RValue::Variable(id) => write!(f, "{}", id),
            RValue::Global(id) => write!(f, "global{}", id),
            RValue::Constant(ref value) => write!(f, "{}", value),
            RValue::Call(id, ref ids) => {
                write!(f, "(call {}", id)?;
                for id in ids {
                    write!(f, " {}", id)?;
                }
                write!(f, ")")
            },
        }
    }
}

#[derive(Debug)]
pub enum Value {
    Integer(i64),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Value::Integer(i) => write!(f, "{}", i),
        }
    }
}

#[derive(Debug)]
pub enum Terminator {
    /// `jump bb(.0)`
    Jump(usize),
    /// `return var(.0)`
    Return(VarId),
    /// A dummy terminator, to be filled in later.
    Dummy,
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Terminator::Jump(i) => write!(f, "(jump bb{})", i),
            Terminator::Return(i) => write!(f, "(return var{})", i.0),
            Terminator::Dummy => write!(f, "<dummy> (THIS IS A BUG!)"),
        }
    }
}

struct MirBuilder<'ctxt> {
    ctxt: &'ctxt Context<'ctxt>,
    bbs: Vec<BasicBlock>,
    bb_idx: usize,
    next_var_id: u32,
    variable_info: Vec<VariableInfo>,
}

#[derive(Debug)]
pub enum MirError {
}

impl<'ctxt> MirBuilder<'ctxt> {
    fn from_context(ctxt: &'ctxt Context) -> Self {
        let mut variable_info = vec![];
        for _ in 0..ctxt.resolution.local_variables {
            variable_info.push(VariableInfo { mutable: true });
        }

        MirBuilder {
            ctxt,
            bbs: vec![BasicBlock::new()],
            bb_idx: 0,
            next_var_id: ctxt.resolution.local_variables,
            variable_info,
        }
    }

    fn new_var_id(&mut self) -> VarId {
        let var_id = self.next_var_id;
        self.variable_info.push(VariableInfo { mutable: false });
        self.next_var_id += 1;
        VarId(var_id)
    }

    fn generate_code(&mut self) -> Result<(), MirError> {
        match self.ctxt.item.kind {
            ItemKind::Function(_, ref body) => {
                let last_id = self.generate_code_from_expr(body)?;
                self.bb().terminator = Terminator::Return(last_id);
                Ok(())
            },
        }
    }

    fn bb(&mut self) -> &mut BasicBlock {
        &mut self.bbs[self.bb_idx]
    }

    fn generate_code_from_expr(&mut self, expr: &Expr) -> Result<VarId, MirError> {
        match expr.kind {
            ExprKind::Integer(i) => {
                let var_id = self.new_var_id();
                let rvalue = RValue::Constant(Value::Integer(i));
                let instruction = Instruction::Assign(var_id, rvalue);
                self.bb().instructions.push(instruction);
                Ok(var_id)
            },
            ExprKind::Ident(ref s) => {
                if let Some(&ResolveId(var_id)) = self.ctxt.resolution.lookup.get(&expr.id) {
                    Ok(VarId(var_id))
                } else if let Some(&global_id) = self.ctxt.globals.get(s) {
                    let var_id = self.new_var_id();
                    let rvalue = RValue::Global(global_id);
                    let instruction = Instruction::Assign(var_id, rvalue);
                    self.bb().instructions.push(instruction);
                    Ok(var_id)
                } else {
                    panic!("internal compiler error: unresolved name was not picked up by coordinator!")
                }
            },
            ExprKind::Let(_, ref what, ref rest) => {
                let var_id = self.generate_code_from_expr(what)?;
                let local_id = self.ctxt.resolution.lookup[&expr.id];
                let rvalue = RValue::Variable(var_id);
                let instruction = Instruction::Assign(VarId(local_id.0), rvalue);
                self.bb().instructions.push(instruction);
                self.generate_code_from_expr(rest)
            },
            ExprKind::SExpr(ref exprs) => {
                let func = &exprs[0];
                let args = &exprs[1..];
                // First, evaluate the arguments in left-to-right order.
                let mut arg_ids = vec![];
                for arg in args {
                    arg_ids.push(self.generate_code_from_expr(arg)?);
                }
                // Next, evaluate the function
                let func_id = self.generate_code_from_expr(func)?;
                // Finally, generate a call instruction
                let var_id = self.new_var_id();
                let rvalue = RValue::Call(func_id, arg_ids);
                let instruction = Instruction::Assign(var_id, rvalue);
                self.bb().instructions.push(instruction);
                Ok(var_id)
            },
        }
    }
}