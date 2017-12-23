use mir::{Mir, VarId, Instruction, RValue, Terminator};
use llvm::{self, Context, Type, Value, Builder};

use std::mem;
use std::collections::HashMap;

struct Codegen<'a> {
    context: &'a mut Context,
    builder: &'a mut Builder,
    mir: &'a Mir,

    function: Value,
    functions: &'a mut [Value],
    global_map: &'a HashMap<usize, usize>,
    bbs: Vec<llvm::BasicBlock>,
    vars: Vec<Option<Value>>,
    stack_vars: Vec<Option<Value>>,
    tmp_vars: u32,
}

impl<'a> Codegen<'a> {
    fn generate(&mut self) {
        for (bb_idx, _) in self.mir.bbs.iter().enumerate() {
            let name = match bb_idx {
                0 => "entry".to_string(),
                i => format!("bb{}", i),
            };
            self.bbs.push(self.context.append_basic_block(self.function, &name));
        }

        self.builder.position_at_end(self.bbs[0]);

        for (i, var) in self.mir.variable_info.iter().enumerate() {
            if var.mutable {
                let name = format!("tmp{}", i);
                let alloca = self.builder.build_alloca(self.context.type_i64(), &name);
                self.stack_vars[i] = Some(alloca);
            }
        }

        for (bb_idx, bb) in self.mir.bbs.iter().enumerate() {
            let llvm_bb = self.bbs[bb_idx];
            self.builder.position_at_end(llvm_bb);

            for instruction in &bb.instructions {
                self.translate_instruction(instruction);
            }

            match bb.terminator {
                Terminator::Jump(to) => {
                    self.builder.build_br(self.bbs[to]);
                },
                Terminator::Return(ref var) => {
                    let ret = self.translate_var(*var);
                    self.builder.build_ret(ret);
                },
                Terminator::Dummy => panic!("internal compiler error: dummy terminator not replaced by codegen!"),
            }
        }
    }

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

    fn translate_instruction(&mut self, instruction: &Instruction) {
        let Instruction::Assign(dest, ref src) = *instruction;
        let name = if self.stack_vars[dest.0 as usize].is_some() {
            self.tmp_vars += 1;
            format!("llvmtmp{}", self.tmp_vars - 1)
        } else {
            format!("tmp{}", dest)
        };
        self.tmp_vars += 1; // FIXME is this necessary?

        let value = match *src {
            RValue::Variable(var) => self.translate_var(var),
            RValue::Constant(::mir::Value::Integer(i)) => self.context.const_i64(i as u64),
            // FIXME assumes globals are all functions
            RValue::Global(i) => self.functions[self.global_map[&i]],
            RValue::Call(func, ref args) => {
                let mut arg_vals = Vec::with_capacity(args.len());
                for &arg in args {
                    let val = self.translate_var(arg);
                    arg_vals.push(val);
                }
                let func_val = self.translate_var(func);
                let call = self.builder.build_call(func_val, &mut arg_vals, &name);
                call
            },
        };

        if let Some(var) = self.stack_vars[dest.0 as usize] {
            self.builder.build_store(value, var);
        } else {
            self.vars[dest.0 as usize] = Some(value);
        }
    }
}

pub fn jit_run(mirs: &[Mir], idx: usize, global_map: HashMap<usize, usize>) -> i64 {
    for mir in mirs {
        // FIXME debug
        println!("{}", mir);
    }

    let mut context = Context::new();
    let mut module = context.create_module_with_name("753");

    let i64_type = context.type_i64();

    let mut functions = vec![];
    for mir in mirs {
        // Currently every function is of type (func () i64)
        let function_type = Type::function_type(i64_type, &mut []);
        functions.push(module.add_function(&mir.name, function_type));
    }

    for (i, mir) in mirs.iter().enumerate() {
        let function = functions[i];
        let mut builder = context.create_builder();
        let mut codegen = Codegen {
            context: &mut context,
            builder: &mut builder,
            mir,

            function,
            functions: &mut functions,
            global_map: &global_map,
            bbs: vec![],
            vars: vec![None; mir.variable_info.len()],
            stack_vars: vec![None; mir.variable_info.len()],
            tmp_vars: 0,
        };
        codegen.generate();
    }

    // FIXME debug
    println!("{}", module);

    let mut ee = module.create_execution_engine().unwrap();

    // FIXME(safety): we assume the function main exists here and has the appropriate signature.
    // For safety reasons we should assert that it exists and is as we expect it to be.
    let name = &mirs[idx].name;
    let addr = ee.get_function_address(name);
    let main: extern "C" fn() -> i64 = unsafe { mem::transmute(addr) };
    main()
}

#[cfg(test)]
mod test {
    use coordinate::Coordinator;

    #[test]
    fn test_basic_codegen() {
        let src = "(define (main) 753)";
        let mut coordinator = Coordinator::from_str(src).unwrap();

        assert_eq!(coordinator.run(), 753);
    }

    #[test]
    fn test_function_calls() {
        let src = "(define (main) (foo)) (define (bar) 42) (define (foo) (bar))";
        let mut coordinator = Coordinator::from_str(src).unwrap();

        assert_eq!(coordinator.run(), 42);
    }

    #[test]
    fn test_eval() {
        let src = "(define (main) (eval (foo))) (define (foo) (eval (bar))) (define (bar) 42)";
        let mut coordinator = Coordinator::from_str(src).unwrap();

        assert_eq!(coordinator.run(), 42)
    }
}