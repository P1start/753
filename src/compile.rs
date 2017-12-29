use parse::{Parser, Expr, ExprKind};
use mir::{self, BasicBlock, Instruction, Terminator, VarId, VariableInfo};
use codemap::{FileId, Span};
use util::Error;
use llvm::{self, Context, Module, Type, Value, Builder, ExecutionEngine};

use rand::{Rng, SeedableRng, StdRng};

use std::collections::{HashMap, HashSet, VecDeque};
use std::collections::hash_map::DefaultHasher;
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Debug)]
pub enum CompileError {
    IncorrectNumberOfArguments(Span, usize),
    IncorrectNumberOfArgumentsAtLeast(Span, usize),
    ExpectedIdent(Span),
    ExpectedList(Span),
    InvalidTopLevelExpr(Span),
}

#[derive(Debug)]
pub struct Compiler<'src> {
    parser: Parser<'src>,

    pub mir_builders: Vec<MirBuilder>,
    dependencies: HashMap<String, Vec<usize>>,
    build_queue: VecDeque<usize>,

    global_ids: HashMap<String, usize>,
    next_global_id: usize,

    rng: StdRng,

    context: Context,
    module: Module,
    functions: Vec<Value>,
    codegens: Vec<Codegen>,

    modules: Vec<Module>,
    ee: ExecutionEngine,
}

#[derive(Debug)]
struct Codegen {
    builder: Builder,

    bbs: Vec<llvm::BasicBlock>,
    vars: Vec<Option<Value>>,
    stack_vars: Vec<Option<Value>>,
    tmp_vars: u32,
}

impl Codegen {
    fn translate_var(&mut self, var: VarId) -> Value {
        let i = var.0;
        if let Some(var) = self.stack_vars[i as usize] {
            let name = format!("llvmtmp{}", self.tmp_vars);
            self.tmp_vars += 1;
            self.builder.build_load(var, &name)
        } else {
            self.vars[i as usize].unwrap()
        }
    }

}

#[derive(Debug)]
pub struct MirBuilder {
    pub bbs: Vec<BasicBlock>,
    pub name: String,

    next_var_id: u32,
    pub variable_info: Vec<VariableInfo>,

    tasks: Vec<Task>,

    locals: HashMap<String, Vec<VarId>>,
    references: HashSet<usize>,

    module_idx: usize,
}

impl fmt::Display for MirBuilder {
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

#[derive(Debug, Clone, PartialEq, Eq)]
enum Task {
    /// Write an instruction to the end of a `BasicBlock`.
    WriteInstruction(usize, Instruction),
    /// Compile an expression at the end of a `BasicBlock` and assign its result to a variable.
    CompileExpr(usize, VarId, Expr),
    DefineLocal(VarId, String),
    RemoveLocal(String),
    WaitOnValue(usize, VarId),
    WaitOnValueWithMirBuilderIdx(usize, VarId, usize),
    WaitOnSymbol,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct LocalId(pub u32);

impl<'src> Compiler<'src> {
    pub fn from_str(s: &'src str) -> Self {
        let mut hasher = DefaultHasher::new();
        s.hash(&mut hasher);
        let seed = hasher.finish();
        let mut context = Context::new();
        let mut module = context.create_module_with_name("753");
        let ee = module.create_execution_engine().unwrap();

        Compiler {
            parser: Parser::from_source(s, FileId(!0)),
            mir_builders: vec![],
            dependencies: HashMap::new(),
            build_queue: VecDeque::new(),
            global_ids: HashMap::new(),
            next_global_id: 0,
            rng: StdRng::from_seed(&[seed as usize]),
            context,
            module,
            functions: vec![],
            codegens: vec![],
            modules: vec![],
            ee,
        }
    }

    fn new_global_id(&mut self) -> usize {
        self.next_global_id += 1;
        self.next_global_id - 1
    }

    pub fn new_opaque_name(&mut self) -> String {
        format!("<{:016x}>", self.rng.next_u64())
    }

    fn new_codegen(&mut self) -> Codegen {
        Codegen {
            builder: self.context.create_builder(),
            bbs: vec![],
            vars: vec![],
            stack_vars: vec![],
            tmp_vars: 0,
        }
    }

    fn add_function(&mut self, mut mir_builder: MirBuilder) -> Result<(), CompileError> {
        let i64_type = self.context.type_i64();
        // FIXME: currently all functions are of type (func () i64)
        let function_type = Type::function_type(i64_type, &mut []);
        let mut new_module = self.context.create_module_with_name(&mir_builder.name);
        let func = new_module.add_function(&mir_builder.name, function_type);
        mir_builder.module_idx = self.modules.len();
        self.modules.push(new_module);
        self.ee.add_module(new_module);

        self.functions.push(func);
        let codegen = self.new_codegen();
        self.codegens.push(codegen);
        self.mir_builders.push(mir_builder);
        Ok(())
    }

    pub fn compile(&mut self) -> Result<(), Error> {
        while !self.parser.is_at_end_of_file() {
            let expr = self.parser.parse_expr()?;
            let mir_builder = self.make_mir_builder(expr)?;
            self.add_function(mir_builder)?;
        }

        for mir_builder_idx in 0..self.mir_builders.len() {
            self.build_queue.push_back(mir_builder_idx);
        }

        while let Some(mir_builder_idx) = self.build_queue.pop_front() {
            println!("Trying to compile {}", mir_builder_idx);
            if let Some(deps) = self.dependencies.get(&self.mir_builders[mir_builder_idx].name) {
                for &dep in deps {
                    self.build_queue.push_back(dep);
                }
            }

            self.partial_compile(mir_builder_idx)?;
        }

        Ok(())
    }

    fn function_is_ready_to_run(&self, idx: usize) -> bool {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(idx);

        while let Some(mir_builder_idx) = queue.pop_front() {
            visited.insert(mir_builder_idx);
            let mir_builder = &self.mir_builders[mir_builder_idx];
            if mir_builder.tasks.len() != 0 {
                return false
            }

            for &reference in &mir_builder.references {
                if !visited.contains(&reference) {
                    queue.push_back(reference);
                }
            }
        }

        true
    }

    fn get_module_for_mir(&mut self, mir_builder_idx: usize) -> Module {
        let idx = self.mir_builders[mir_builder_idx].module_idx;
        self.modules[idx]
    }

    fn run_function(&mut self, mir_builder_idx: usize) -> i64 {
        let module = self.get_module_for_mir(mir_builder_idx);
        self.ee.add_module(module);
        for (i, module) in self.modules.iter().enumerate() {
            println!("=== MODULE {} ===\n{}\n=== END MODULE {0} ===", i, module);
        }
        let res = {
            let name = &self.mir_builders[mir_builder_idx].name;
            // FIXME(safety): we assume the function has the appropriate signature.
            // For safety reasons we should assert that it is as we expect it to be.
            let func: extern "C" fn() -> i64 = unsafe { self.ee.get_function(name) }.unwrap();
            func()
        };
        res
    }

    pub fn run(&mut self) -> i64 {
        println!("=== MODULE ===\n{}\n=== END MODULE ===", self.module);
        // FIXME(copypaste): from Compiler::run_function
        let func: extern "C" fn() -> i64 = unsafe { self.ee.get_function("main") }.unwrap();
        let ret = func();
        ret
    }

    fn partial_compile(&mut self, mir_builder_idx: usize) -> Result<(), CompileError> {
        while self.mir_builders[mir_builder_idx].tasks.len() != 0 {
            // We have to do a lot of ugly things in this function to get around rust-lang/rust#6393.
            enum Continue {
                CreateTemporaryFunction(Expr),
                TryToEvaluateFunction(usize, VarId, usize),
            }
            let which;
            {
                let mir_builder_len = self.mir_builders.len();
                let mir_builder = &mut self.mir_builders[mir_builder_idx];
                let next = mir_builder.next()?;

                match next {
                    CompileExitStatus::WaitingOnSymbol { name, bb_idx, var } => {
                        if let Some(&global_id) = self.global_ids.get(&name) {
                            // Remove Task::WaitOnSymbol
                            debug_assert_eq!(mir_builder.tasks.pop(), Some(Task::WaitOnSymbol));

                            let instruction = Instruction::Global(var, global_id);
                            mir_builder.tasks.push(Task::WriteInstruction(bb_idx, instruction));
                            mir_builder.references.insert(global_id);
                        } else {
                            // Add the name as a dependency
                            if self.dependencies.contains_key(&name) {
                                let deps = self.dependencies.get_mut(&name).unwrap();
                                deps.push(mir_builder_idx);
                            } else {
                                if !self.dependencies.contains_key(&name) {
                                    self.dependencies.insert(name, vec![mir_builder_idx]);
                                } else {
                                    self.dependencies.get_mut(&name).unwrap().push(mir_builder_idx);
                                }
                            }
                        }
                        continue
                    },
                    CompileExitStatus::NothingToDo => continue,
                    CompileExitStatus::WaitingOnValue { expr } => {
                        let old_task = mir_builder.tasks.pop();
                        match old_task {
                            Some(Task::WaitOnValue(bb_idx, var)) => {
                                mir_builder.tasks.push(Task::WaitOnValueWithMirBuilderIdx(bb_idx, var, mir_builder_len));
                            },
                            _ => panic!(),
                        }
                        which = Continue::CreateTemporaryFunction(expr);
                    },
                    CompileExitStatus::StillWaitingOnValue { mir_builder_idx: mbi2, bb_idx, var } => {
                        which = Continue::TryToEvaluateFunction(bb_idx, var, mbi2);
                    },
                }
            }

            match which {
                Continue::CreateTemporaryFunction(expr) => {
                    let new_name = self.new_opaque_name();
                    self.build_queue.push_back(self.mir_builders.len());
                    let mut new_mir = MirBuilder::new(new_name, expr);
                    self.add_function(new_mir)?;

                    self.build_queue.push_back(mir_builder_idx);
                    break
                },
                Continue::TryToEvaluateFunction(bb_idx, var, mbi2) => {
                    if self.function_is_ready_to_run(mbi2) {
                        let result = self.run_function(mbi2);
                        let mir_builder = &mut self.mir_builders[mir_builder_idx];
                        match mir_builder.tasks.pop() {
                            Some(Task::WaitOnValueWithMirBuilderIdx(..)) => {},
                            _ => panic!(),
                        }
                        // TODO: actually evaluate thing
                        mir_builder.tasks.push(Task::WriteInstruction(bb_idx, Instruction::Constant(var, mir::Value::Integer(result))));
                        continue
                    } else {
                        self.build_queue.push_back(mir_builder_idx);
                        break
                    }
                },
            }
        }

        if self.mir_builders[mir_builder_idx].tasks.len() == 0 {
            self.generate_code_for_funtion(mir_builder_idx);
        }

        Ok(())
    }

    fn generate_code_for_funtion(&mut self, mir_builder_idx: usize) {
        let mir = &self.mir_builders[mir_builder_idx];
        let codegen = &mut self.codegens[mir_builder_idx];
        let function = self.functions[mir_builder_idx];

        let idx = mir.module_idx;
        let mut module = self.modules[idx];
        for &reference in &mir.references {
            let name = &self.mir_builders[reference].name;
            let i64_ty = self.context.type_i64();
            let function_ty = Type::function_type(i64_ty, &mut []);
            module.add_function(name, function_ty);
        }

        codegen.stack_vars = vec![None; mir.variable_info.len()];
        codegen.vars = vec![None; mir.variable_info.len()];

        for (bb_idx, _) in mir.bbs.iter().enumerate() {
            let name = match bb_idx {
                0 => "entry".to_string(),
                i => format!("bb{}", i),
            };
            codegen.bbs.push(self.context.append_basic_block(function, &name));
        }

        codegen.builder.position_at_end(codegen.bbs[0]);

        for (i, var) in mir.variable_info.iter().enumerate() {
            if var.mutable {
                let name = format!("tmp{}", i);
                let alloca = codegen.builder.build_alloca(self.context.type_i64(), &name);
                codegen.stack_vars[i] = Some(alloca);
            }
        }

        for (bb_idx, bb) in mir.bbs.iter().enumerate() {
            let llvm_bb = codegen.bbs[bb_idx];
            codegen.builder.position_at_end(llvm_bb);

            for instruction in &bb.instructions {
                codegen.tmp_vars += 1; // FIXME is this necessary?
        
                let (dest, value) = match *instruction {
                    Instruction::Variable(dest, var) => (dest, codegen.translate_var(var)),
                    Instruction::Constant(dest, ::mir::Value::Integer(i)) => (dest, self.context.const_i64(i as u64)),
                    // FIXME assumes globals are all functions
                    Instruction::Global(dest, i) => {
                        let function = unsafe {
                            self.modules[idx].get_function(&self.mir_builders[i].name)
                        };
                        (dest, function)
                    },
                    Instruction::Call(dest, func, ref args) => {
                        let mut arg_vals = Vec::with_capacity(args.len());
                        for &arg in args {
                            let val = codegen.translate_var(arg);
                            arg_vals.push(val);
                        }
                        let func_val = codegen.translate_var(func);
        
                        let name = if codegen.stack_vars[dest.0 as usize].is_some() {
                            codegen.tmp_vars += 1;
                            format!("llvmtmp{}", codegen.tmp_vars - 1)
                        } else {
                            format!("tmp{}", dest)
                        };
                        let call = codegen.builder.build_call(func_val, &mut arg_vals, &name);
                        (dest, call)
                    },
                };
        
                if let Some(var) = codegen.stack_vars[dest.0 as usize] {
                    codegen.builder.build_store(value, var);
                } else {
                    codegen.vars[dest.0 as usize] = Some(value);
                }
            }

            match bb.terminator {
                Terminator::Jump(to) => {
                    codegen.builder.build_br(codegen.bbs[to]);
                },
                Terminator::Return(ref var) => {
                    let ret = codegen.translate_var(*var);
                    codegen.builder.build_ret(ret);
                },
            }
        }
    }

    fn make_mir_builder(&mut self, expr: Expr) -> Result<MirBuilder, CompileError> {
        match expr.kind {
            ExprKind::List(mut exprs) => {
                match exprs[0].kind {
                    ExprKind::Ident(ref s) if s == "define" => {},
                    _ => return Err(CompileError::InvalidTopLevelExpr(expr.span)),
                }

                if exprs.len() != 3 {
                    return Err(CompileError::IncorrectNumberOfArguments(expr.span, 3))
                }

                let name = match exprs.remove(1).kind {
                    ExprKind::List(mut arg_exprs) => {
                        if arg_exprs.len() != 1 {
                            // TODO support function arguments
                            return Err(CompileError::IncorrectNumberOfArguments(exprs[1].span, 1))
                        }
                        match arg_exprs.remove(0).kind {
                            ExprKind::Ident(s) => s,
                            _ => return Err(CompileError::ExpectedIdent(arg_exprs[1].span)),
                        }
                    },
                    _ => return Err(CompileError::ExpectedList(exprs[1].span)),
                };

                let new_global_id = self.new_global_id();
                self.global_ids.insert(name.clone(), new_global_id);

                let body = exprs.remove(1);
                Ok(MirBuilder::new(name, body))
            },
            _ => return Err(CompileError::ExpectedList(expr.span)),
        }
    }
}

enum CompileExitStatus {
    WaitingOnSymbol {
        name: String,
        bb_idx: usize,
        var: VarId,
    },
    WaitingOnValue {
        expr: Expr,
    },
    StillWaitingOnValue {
        mir_builder_idx: usize,
        bb_idx: usize,
        var: VarId,
    },
    NothingToDo,
}

impl MirBuilder {
    pub fn new(name: String, body: Expr) -> Self {
        let var_id = VarId(0);

        let bb = BasicBlock {
            instructions: vec![],
            terminator: Terminator::Return(var_id),
        };

        MirBuilder {
            bbs: vec![bb],
            name,
            next_var_id: 1,
            variable_info: vec![VariableInfo { mutable: false }],
            locals: HashMap::new(),
            tasks: vec![Task::CompileExpr(0, var_id, body)],
            references: HashSet::new(),
            module_idx: !0,
        }
    }

    fn new_var_id(&mut self, mutable: bool) -> VarId {
        let var_id = self.next_var_id;
        self.next_var_id += 1;
        self.variable_info.push(VariableInfo { mutable });
        VarId(var_id)
    }

    fn next(&mut self) -> Result<CompileExitStatus, CompileError> {
        let task = self.tasks.pop().unwrap();
        match task {
            Task::CompileExpr(bb_idx, var, e) => match e.kind {
                ExprKind::Integer(i) => {
                    let new_instruction = Instruction::Constant(var, mir::Value::Integer(i));
                    let new_task = Task::WriteInstruction(bb_idx, new_instruction);
                    self.tasks.push(new_task);
                },
                ExprKind::List(mut exprs) => {
                    let kind = match exprs.get(0) {
                        Some(&Expr { kind: ExprKind::Ident(ref s), .. }) if s == "let" => 1,
                        Some(&Expr { kind: ExprKind::Ident(ref s), .. }) if s == "eval" => 2,
                        _ => 0,
                    };
                    if kind == 1 { // let
                        if exprs.len() != 3 {
                            return Err(CompileError::IncorrectNumberOfArguments(e.span, 3))
                        }
                
                        let rest = exprs.pop().unwrap();
                        let assign = exprs.pop().unwrap();
                
                        match assign.kind {
                            ExprKind::List(mut es) => {
                                if es.len() != 2 {
                                    return Err(CompileError::IncorrectNumberOfArguments(assign.span, 2))
                                }
                
                                let value = es.pop().unwrap();
                                let name = self.expect_ident(es.pop().unwrap())?;
                                
                                let new_var_id = self.new_var_id(true);
                                self.tasks.push(Task::RemoveLocal(name.clone()));
                                self.tasks.push(Task::CompileExpr(bb_idx, var, rest));
                                self.tasks.push(Task::DefineLocal(new_var_id, name));
                                self.tasks.push(Task::CompileExpr(bb_idx, new_var_id, value));
                            },
                            _ => return Err(CompileError::ExpectedList(assign.span)),
                        }
                    } else if kind == 2 { // eval
                        if exprs.len() != 2 {
                            return Err(CompileError::IncorrectNumberOfArguments(e.span, 2))
                        }
                        let inner = exprs.pop().unwrap();
                        self.tasks.push(Task::WaitOnValue(bb_idx, var));
                        return Ok(CompileExitStatus::WaitingOnValue {
                            expr: inner,
                        })
                    } else {
                        if exprs.len() == 0 {
                            return Err(CompileError::IncorrectNumberOfArgumentsAtLeast(e.span, 1))
                        }
                        let func = exprs.remove(0);
                        let func_var = self.new_var_id(false);
                        let mut arg_vars = vec![];
                        for _ in 0..exprs.len() {
                            arg_vars.push(self.new_var_id(false));
                        }
                        // FIXME: unnecessary clone
                        let call_instruction = Instruction::Call(var, func_var, arg_vars.clone());
                        self.tasks.push(Task::WriteInstruction(bb_idx, call_instruction));
                        self.tasks.push(Task::CompileExpr(bb_idx, func_var, func));
                        for &arg_var in arg_vars.iter().rev() {
                            self.tasks.push(Task::CompileExpr(bb_idx, arg_var, exprs.pop().unwrap()));
                        }
                    }
                },
                ExprKind::Ident(s) => {
                    if let Some(&this_var) = self.locals.get(&s).and_then(|x| x.last()) {
                        self.tasks.push(Task::WriteInstruction(bb_idx, Instruction::Variable(var, this_var)));
                    } else {
                        self.tasks.push(Task::WaitOnSymbol);
                        return Ok(CompileExitStatus::WaitingOnSymbol {
                            name: s,
                            bb_idx,
                            var,
                        })
                    }
                },
            },
            Task::WriteInstruction(bb_idx, instruction) => self.bbs[bb_idx].instructions.push(instruction),
            Task::DefineLocal(new_var_id, name) => {
                if !self.locals.contains_key(&name) {
                    self.locals.insert(name, vec![new_var_id]);
                } else {
                    self.locals.get_mut(&name).unwrap().push(new_var_id);
                }
            },
            Task::RemoveLocal(name) => {
                self.locals.get_mut(&name).unwrap().pop();
            },
            Task::WaitOnValue(..) => panic!(),
            Task::WaitOnValueWithMirBuilderIdx(bb_idx, var, mir_builder_idx) => {
                self.tasks.push(task.clone());
                return Ok(CompileExitStatus::StillWaitingOnValue {
                    mir_builder_idx,
                    bb_idx,
                    var,
                })
            },
            Task::WaitOnSymbol => {
                self.tasks.push(Task::WaitOnSymbol);
                return Ok(CompileExitStatus::NothingToDo)
            },
        }

        Ok(CompileExitStatus::NothingToDo)
    }

    fn expect_ident(&mut self, expr: Expr) -> Result<String, CompileError> {
        match expr.kind {
            ExprKind::Ident(s) => Ok(s),
            _ => return Err(CompileError::ExpectedIdent(expr.span)),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_let() {
        let src = "(define (main) (let (x 1)))";
        let mut compiler = Compiler::from_str(src);
        let result = compiler.compile();
        let span = Span { lo: 15, hi: 26, file: FileId(!0) };
        match result {
            Err(Error::CompileError(CompileError::IncorrectNumberOfArguments(span_actual, 3))) if span_actual == span => {},
            _ => panic!(),
        }
    }
    /*
    // These tests don't seem to run properly, unfortunately
    #[test]
    fn test_basic_codegen() {
        let src = "(define (main) 753)";
        let mut compiler = Compiler::from_str(src);
        compiler.compile().unwrap();

        assert_eq!(compiler.run(), 753);
    }

    #[test]
    fn test_function_calls() {
        let src = "(define (main) (foo)) (define (bar) 42) (define (foo) (bar))";
        let mut compiler = Compiler::from_str(src);
        compiler.compile().unwrap();

        assert_eq!(compiler.run(), 42);
    }

    #[test]
    fn test_eval() {
        let src = "(define (main) (eval (foo))) (define (foo) (eval (bar))) (define (bar) 42)";
        let mut compiler = Compiler::from_str(src);
        compiler.compile().unwrap();

        assert_eq!(compiler.run(), 42)
    }*/
}