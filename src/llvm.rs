//! Some (mostly) safe LLVM bindings.

use llvm_sys::core::*;
use llvm_sys::execution_engine::*;
use llvm_sys::target::*;
use llvm_sys::analysis::*;
use llvm_sys::prelude::*;

use std::ffi::{CString, CStr};
use std::mem;
use std::fmt;

#[repr(C)]
pub struct Context(LLVMContextRef);
impl fmt::Debug for Context {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "<llvm::Context>") }
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Module(LLVMModuleRef);
impl fmt::Debug for Module {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "<llvm::Module>") }
}

#[repr(C)]
pub struct Builder(LLVMBuilderRef);
impl fmt::Debug for Builder {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "<llvm::Builder>") }
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Type(LLVMTypeRef);
impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "<llvm::Type>") }
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Value(LLVMValueRef);
impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "<llvm::Value>") }
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct BasicBlock(LLVMBasicBlockRef);
impl fmt::Debug for BasicBlock {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "<llvm::BasicBlock>") }
}

#[repr(C)]
pub struct ExecutionEngine(LLVMExecutionEngineRef);
impl fmt::Debug for ExecutionEngine {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "<llvm::ExecutionEngine>") }
}

impl Context {
    pub fn new() -> Context {
        unsafe {
            Context(LLVMContextCreate())
        }
    }

    pub fn create_module_with_name(&mut self, name: &str) -> Module {
        let c_name = CString::new(name).unwrap();
        unsafe {
            Module(LLVMModuleCreateWithNameInContext(c_name.as_ptr(), self.0))
        }
    }

    pub fn create_builder(&mut self) -> Builder {
        unsafe {
            Builder(LLVMCreateBuilderInContext(self.0))
        }
    }

    pub fn type_i64(&mut self) -> Type {
        unsafe {
            Type(LLVMInt64TypeInContext(self.0))
        }
    }

    pub fn const_i64(&mut self, v: u64) -> Value {
        unsafe {
            Value(LLVMConstInt(self.type_i64().0, v, 1))
        }
    }

    pub fn append_basic_block(&mut self, function: Value, name: &str) -> BasicBlock {
        let c_name = CString::new(name).unwrap();
        unsafe {
            BasicBlock(LLVMAppendBasicBlockInContext(self.0, function.0, c_name.as_ptr()))
        }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe {
            LLVMContextDispose(self.0);
        }
    }
}

impl Module {
    pub fn add_function(&mut self, name: &str, function_type: Type) -> Value {
        let c_name = CString::new(name).unwrap();
        unsafe {
            Value(LLVMAddFunction(self.0, c_name.as_ptr(), function_type.0))
        }
    }

    pub fn verify(&mut self) -> Result<(), String> {
        unsafe {
            let mut err = mem::zeroed();
            if LLVMVerifyModule(self.0, LLVMVerifierFailureAction::LLVMReturnStatusAction, &mut err) != 0 {
                let string = CStr::from_ptr(err).to_str().unwrap().into();
                LLVMDisposeMessage(err);
                Err(string)
            } else {
                Ok(())
            }
        }
    }

    pub fn create_execution_engine(&mut self) -> Result<ExecutionEngine, String> {
        self.verify()?;
        unsafe {
            LLVMLinkInMCJIT();
            if LLVM_InitializeNativeTarget() != 0 {
                return Err("could not initialize native target".to_string())
            }
            if LLVM_InitializeNativeAsmPrinter() != 0 {
                return Err("could not initialize native ASM printer".to_string())
            }
            let mut ee = mem::uninitialized();
            let mut err = mem::zeroed();

            if LLVMCreateExecutionEngineForModule(&mut ee, self.0, &mut err) != 0 {
                let string = CStr::from_ptr(err).to_str().unwrap().into();
                LLVMDisposeMessage(err);
                Err(string)
            } else {
                Ok(ExecutionEngine(ee))
            }
        }
    }

    pub unsafe fn get_function(&mut self, name: &str) -> Value {
        let c_str = CString::new(name).unwrap();
        let val = LLVMGetNamedFunction(self.0, c_str.as_ptr());
        Value(val)
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe {
            let str_ptr = LLVMPrintModuleToString(self.0);
            let c_str = CStr::from_ptr(str_ptr);
            try!(write!(f, "{}", c_str.to_str().unwrap()));
            LLVMDisposeMessage(str_ptr);
            Ok(())
        }
    }
}

impl Builder {
    pub fn position_at_end(&mut self, bb: BasicBlock) {
        unsafe {
            LLVMPositionBuilderAtEnd(self.0, bb.0);
        }
    }

    pub fn build_call(&mut self, func: Value, args: &mut [Value], dest_name: &str) -> Value {
        let c_name = CString::new(dest_name).unwrap();
        unsafe {
            let raw_args: *mut LLVMValueRef = mem::transmute(args.as_mut_ptr());
            // FIXME: this u32 should be something in libc
            Value(LLVMBuildCall(self.0, func.0, raw_args, args.len() as u32, c_name.as_ptr()))
        }
    }

    pub fn build_alloca(&mut self, ty: Type, dest_name: &str) -> Value {
        let c_name = CString::new(dest_name).unwrap();
        unsafe {
            Value(LLVMBuildAlloca(self.0, ty.0, c_name.as_ptr()))
        }
    }

    pub fn build_load(&mut self, ptr: Value, dest_name: &str) -> Value {
        let c_name = CString::new(dest_name).unwrap();
        unsafe {
            Value(LLVMBuildLoad(self.0, ptr.0, c_name.as_ptr()))
        }
    }

    pub fn build_store(&mut self, val: Value, ptr: Value) -> Value {
        unsafe {
            Value(LLVMBuildStore(self.0, val.0, ptr.0))
        }
    }

    pub fn build_ret(&mut self, value: Value) -> Value {
        unsafe {
            Value(LLVMBuildRet(self.0, value.0))
        }
    }

    pub fn build_br(&mut self, to: BasicBlock) -> Value {
        unsafe {
            Value(LLVMBuildBr(self.0, to.0))
        }
    }
}

impl Drop for Builder {
    fn drop(&mut self) {
        unsafe {
            LLVMDisposeBuilder(self.0);
        }
    }
}

impl Type {
    pub fn function_type(ret_type: Type, arg_types: &mut [Type]) -> Type {
        unsafe {
            Type(LLVMFunctionType(ret_type.0, mem::transmute(arg_types.as_mut_ptr()), arg_types.len() as _, 0))
        }
    }
}

impl Value {
    pub fn undef(ty: Type) -> Value {
        unsafe {
            Value(LLVMGetUndef(ty.0))
        }
    }

    // FIXME this u32 is probably platform-dependent and should be something in libc
    pub unsafe fn count_params(&mut self) -> u32 {
        LLVMCountParams(self.0)
    }

    pub unsafe fn get_params(&mut self) -> Vec<Value> {
        let param_count = self.count_params() as usize;
        let mut v: Vec<Value> = Vec::with_capacity(param_count);
        let v_ref = mem::transmute::<*mut Value, *mut LLVMValueRef>(v.as_mut_ptr());
        LLVMGetParams(self.0, v_ref);
        v.set_len(param_count);
        v
    }
}

impl ExecutionEngine {
    pub fn get_function_address(&mut self, name: &str) -> u64 {
        let c_name = CString::new(name).unwrap();
        unsafe {
            LLVMGetFunctionAddress(self.0, c_name.as_ptr())
        }
    }

    pub unsafe fn get_function<F: Copy>(&mut self, name: &str) -> Option<F> {
        let c_name = CString::new(name).unwrap();
        let ptr = LLVMGetFunctionAddress(self.0, c_name.as_ptr());
        if ptr == 0 { None }
        else { Some(*(&ptr as *const _ as *const F)) }
    }

    pub fn add_module(&mut self, module: Module) {
        unsafe {
            LLVMAddModule(self.0, module.0)
        }
    }

    pub fn remove_module(&mut self, module: Module) -> Result<(), String> {
        unsafe {
            let mut err = mem::zeroed();
            let mut out_module = mem::uninitialized();
            if LLVMRemoveModule(self.0, module.0, &mut out_module, &mut err) != 0 {
                let string = CStr::from_ptr(err).to_str().unwrap().into();
                LLVMDisposeMessage(err);
                Err(string)
            } else {
                Ok(())
            }
        }
    }
}

impl Drop for ExecutionEngine {
    fn drop(&mut self) {
        unsafe {
            LLVMDisposeExecutionEngine(self.0);
        }
    }
}
