use crate::middleend::ir::module::{
    CallTarget, IRBasicBlock, IRFunction, IRInstruction, IRInstructionKind, IRModule, IRType,
    IRValue,
};
use std::{
    fmt::Write,
    fs,
    io::{self, Write as IoWrite},
    path::Path,
    process::{Command, Stdio},
    sync::mpsc::{self, RecvTimeoutError},
    thread,
    time::Duration,
};

use tempfile::Builder;

pub fn emit_module(module: &IRModule) -> String {
    let mut emitter = LLVMEmitter::new();
    emitter.emit_module(module);
    emitter.finish()
}

struct LLVMEmitter {
    output: String,
}

/// Attempt to validate emitted LLVM IR using the `llvm-as` binary.
///
/// If `llvm-as` is not available in the current PATH, validation is skipped and the function
/// returns `Ok(())` after emitting a warning. Any other I/O error or a non-zero exit status from
/// `llvm-as` is reported as an error.
pub fn validate_with_llvm_as(llvm_ir: &str) -> Result<(), String> {
    let mut cmd = Command::new("llvm-as");
    cmd.arg("-o")
        .arg("/dev/null")
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::piped());
    let mut child = match cmd.spawn() {
        Ok(child) => child,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            eprintln!("Warning: 'llvm-as' not found in PATH. Skipping LLVM IR validation.");
            return Ok(());
        }
        Err(e) => return Err(format!("Failed to spawn 'llvm-as': {}", e)),
    };

    if let Some(stdin) = child.stdin.as_mut() {
        stdin
            .write_all(llvm_ir.as_bytes())
            .map_err(|e| format!("Failed to write LLVM IR to 'llvm-as' stdin: {}", e))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("Failed to wait for 'llvm-as' to finish: {}", e))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("'llvm-as' reported errors:\n{}", stderr));
    }

    Ok(())
}

const RUNTIME_LL_PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/runtime/runtime.ll");

#[derive(Debug, Clone)]
pub struct ExecutionResult {
    pub stdout: String,
    pub stderr: String,
    pub exit_code: i32,
}

pub fn compile_and_run_ir(
    ir: &str,
    stdin_data: &[u8],
    timeout: Duration,
) -> Result<ExecutionResult, String> {
    let temp_dir = Builder::new()
        .prefix("rcompiler_temp")
        .tempdir()
        .map_err(|e| format!("Failed to create temporary directory: {}", e))?;

    let ir_path = temp_dir.path().join("module.ll");
    fs::write(&ir_path, ir).map_err(|e| format!("Failed to write {}: {e}", ir_path.display()))?;

    let runtime_path = Path::new(RUNTIME_LL_PATH);
    if !runtime_path.exists() {
        return Err(format!(
            "Runtime file not found at {}",
            runtime_path.display()
        ));
    }

    let exe_path = temp_dir.path().join("program");
    let clang_output = Command::new("clang")
        .arg("-O0")
        .arg("-Wno-override-module")
        .arg(&ir_path)
        .arg(runtime_path)
        .arg("-o")
        .arg(&exe_path)
        // Set stack size to 16 MB for large struct tests
        .arg("-Wl,-stack_size,0x1000000") // 16 MB on macOS
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .output()
        .map_err(|err| match err.kind() {
            io::ErrorKind::NotFound => "Clang not found in PATH.".to_string(),
            _ => format!("Failed to execute clang: {}", err),
        })?;

    if !clang_output.status.success() {
        let stderr = String::from_utf8_lossy(&clang_output.stderr);
        return Err(format!("Clang compilation failed:\n{}", stderr));
    }

    let mut child = Command::new(&exe_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("Failed to spawn executable: {}", e))?;

    if !stdin_data.is_empty() {
        if let Some(stdin) = child.stdin.as_mut() {
            stdin
                .write_all(stdin_data)
                .map_err(|e| format!("Failed to write to executable stdin: {}", e))?;
        }
    }
    drop(child.stdin.take());

    let pid = child.id();
    let exe_display = exe_path.display().to_string();
    let (tx, rx) = mpsc::channel();
    let wait_handle = thread::spawn(move || {
        let result = child.wait_with_output();
        let _ = tx.send(result);
    });

    let output = match rx.recv_timeout(timeout) {
        Ok(result) => {
            let output = result.map_err(|e| format!("Failed to wait for executable: {}", e))?;
            let _ = wait_handle.join();
            output
        }

        Err(RecvTimeoutError::Timeout) => {
            terminate_process(pid);
            let _ = wait_handle.join();
            return Err(format!(
                "Execution of '{}' timed out after {:?}",
                exe_display, timeout
            ));
        }

        Err(RecvTimeoutError::Disconnected) => {
            let _ = wait_handle.join();
            return Err(format!(
                "Execution of '{}' failed: channel disconnected",
                exe_display
            ));
        }
    };

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let exit_code = output.status.code().unwrap_or(-1);

    Ok(ExecutionResult {
        stdout,
        stderr,
        exit_code,
    })
}

#[cfg(unix)]
fn terminate_process(pid: u32) {
    unsafe {
        let _ = libc::kill(pid as libc::pid_t, libc::SIGKILL);
    }
}

#[cfg(not_unix)]
fn terminate_process(_pid: u32) {
    // On non-Unix systems, process termination is not implemented.
}

impl LLVMEmitter {
    pub fn new() -> Self {
        Self {
            output: String::new(),
        }
    }

    pub fn finish(self) -> String {
        self.output
    }

    fn emit_module(&mut self, module: &IRModule) {
        if !module.name.is_empty() {
            let _ = writeln!(self.output, "; ModuleID = '{}'", module.name);
            let _ = writeln!(self.output, "source_filename = \"{}\"\n", module.name);
            self.output.push('\n');
        }

        for (idx, func) in module.funcs.iter().enumerate() {
            self.emit_function(func);
            if idx + 1 < module.funcs.len() {
                self.output.push('\n');
            }
        }
    }

    fn emit_function(&mut self, func: &IRFunction) {
        let params = func
            .params
            .iter()
            .map(|(name, ty)| {
                format!(
                    "{} {}",
                    self.format_type(ty),
                    self.format_argument_name(name)
                )
            })
            .collect::<Vec<_>>()
            .join(", ");

        if func.basic_blocks.is_empty() {
            let _ = writeln!(
                self.output,
                "declare {} @{}({})",
                self.format_type(&func.return_type),
                func.name,
                params
            );
            return;
        }

        let _ = writeln!(
            self.output,
            "define {} @{}({}) {{",
            self.format_type(&func.return_type),
            func.name,
            params
        );

        for block in &func.basic_blocks {
            self.emit_block(block);
        }

        self.output.push_str("}\n");
    }

    fn emit_block(&mut self, block: &IRBasicBlock) {
        let _ = writeln!(self.output, "{}:", block.label);

        for inst in &block.instructions {
            let line = self.format_instruction(inst);
            let _ = writeln!(self.output, "  {}", line);
        }

        if let Some(terminator) = &block.terminator {
            let line = self.format_instruction(terminator);
            let _ = writeln!(self.output, "  {}", line);
        }
    }

    fn format_instruction(&self, inst: &IRInstruction) -> String {
        let mut parts = String::new();
        if let Some(result) = &inst.result {
            parts.push_str(&format!("{} = ", self.format_value(result)));
        }
        match &inst.kind {
            IRInstructionKind::Alloca { alloc_type, align } => {
                parts.push_str("alloca ");
                parts.push_str(&self.format_type(alloc_type));
                if let Some(align) = align {
                    parts.push_str(&format!(", align {}", align));
                }
            }
            IRInstructionKind::Load { ptr, align } => {
                let ty = inst.ty.as_ref().expect("Load instruction must have a type");
                parts.push_str(&format!(
                    "load {}, {} {}",
                    self.format_type(ty),
                    self.format_type(&IRType::Ptr(Box::new(ty.clone()))),
                    self.format_value(ptr)
                ));
                if let Some(align) = align {
                    parts.push_str(&format!(", align {}", align));
                }
            }
            IRInstructionKind::Store { value, ptr, align } => {
                parts.push_str(&format!(
                    "store {} {}, {} {}",
                    self.format_type(&value.get_type()),
                    self.format_value(value),
                    self.format_type(&ptr.get_type()),
                    self.format_value(ptr)
                ));
                if let Some(align) = align {
                    parts.push_str(&format!(", align {}", align));
                }
            }
            IRInstructionKind::GetElementPtr {
                base,
                indices,
                in_bounds,
            } => {
                if *in_bounds {
                    parts.push_str("getelementptr inbounds ");
                } else {
                    parts.push_str("getelementptr ");
                }
                let elem_ty = match &base.get_type() {
                    IRType::Ptr(inner) => self.format_type(inner),
                    other => self.format_type(other),
                };
                parts.push_str(&format!(
                    "{}, {} {}",
                    elem_ty,
                    self.format_type(&base.get_type()),
                    self.format_value(base)
                ));
                for idx in indices {
                    parts.push_str(&format!(
                        ", {} {}",
                        self.format_type(&idx.get_type()),
                        self.format_value(idx)
                    ));
                }
            }
            IRInstructionKind::Binary { op, lhs, rhs } => {
                parts.push_str(&format!(
                    "{} {} {}, {}",
                    *op,
                    self.format_type(&lhs.get_type()),
                    self.format_value(lhs),
                    self.format_value(rhs)
                ));
            }
            IRInstructionKind::ICmp { op, lhs, rhs } => {
                parts.push_str(&format!(
                    "icmp {} {} {}, {}",
                    *op,
                    self.format_type(&lhs.get_type()),
                    self.format_value(lhs),
                    self.format_value(rhs)
                ));
            }
            IRInstructionKind::Cast { op, value, to_type } => {
                parts.push_str(&format!(
                    "{} {} {} to {}",
                    *op,
                    self.format_type(&value.get_type()),
                    self.format_value(value),
                    self.format_type(to_type)
                ));
            }
            IRInstructionKind::Br { dest } => {
                parts.push_str(&format!("br label %{}", dest));
            }
            IRInstructionKind::CondBr {
                cond,
                then_dest,
                else_dest,
            } => {
                parts.push_str(&format!(
                    "br {} {}, label %{}, label %{}",
                    self.format_type(&cond.get_type()),
                    self.format_value(cond),
                    then_dest,
                    else_dest
                ));
            }
            IRInstructionKind::Call { callee, args } => {
                let callee_str = match callee {
                    CallTarget::Direct(name) => format!("@{}", name),
                    CallTarget::Indirect(value) => self.format_value(value),
                };
                let args_str = args
                    .iter()
                    .map(|arg| {
                        format!(
                            "{} {}",
                            self.format_type(&arg.get_type()),
                            self.format_value(arg)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", ");

                if let Some(ret_ty) = &inst.ty {
                    parts.push_str(&format!(
                        "call {} {}({})",
                        self.format_type(ret_ty),
                        callee_str,
                        args_str
                    ));
                } else {
                    parts.push_str(&format!("call void {}({})", callee_str, args_str));
                }
            }
            IRInstructionKind::Ret { value } => {
                if let Some(value) = value {
                    parts.push_str(&format!(
                        "ret {} {}",
                        self.format_type(&value.get_type()),
                        self.format_value(value)
                    ));
                } else {
                    parts.push_str("ret void");
                }
            }
            IRInstructionKind::Phi { ty, incomings } => {
                parts.push_str(&format!("phi {} ", self.format_type(ty)));
                if incomings.is_empty() {
                    parts.push_str("[]");
                } else {
                    for (i, (val, label)) in incomings.iter().enumerate() {
                        if i > 0 {
                            parts.push_str(", ");
                        }
                        parts.push_str(&format!("[ {}, %{} ]", self.format_value(val), label));
                    }
                }
            }
            IRInstructionKind::Select {
                cond,
                true_val,
                false_val,
            } => {
                let ty = inst
                    .ty
                    .as_ref()
                    .expect("Select instruction must have a type");
                parts.push_str(&format!(
                    "select {} {}, {} {}, {} {}",
                    self.format_type(&cond.get_type()),
                    self.format_value(cond),
                    self.format_type(ty),
                    self.format_value(true_val),
                    self.format_type(ty),
                    self.format_value(false_val)
                ));
            }
            IRInstructionKind::ExtractValue { aggregate, indices } => {
                let indices_str = indices
                    .iter()
                    .map(|idx| idx.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                parts.push_str(&format!(
                    "extractvalue {} {}, {}",
                    self.format_type(&aggregate.get_type()),
                    self.format_value(aggregate),
                    indices_str
                ));
            }
            IRInstructionKind::InsertValue {
                aggregate,
                value,
                indices,
            } => {
                let indices_str = indices
                    .iter()
                    .map(|idx| idx.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                parts.push_str(&format!(
                    "insertvalue {} {}, {} {}, {}",
                    self.format_type(&aggregate.get_type()),
                    self.format_value(aggregate),
                    self.format_type(&value.get_type()),
                    self.format_value(value),
                    indices_str
                ));
            }
        }
        parts
    }

    fn format_type(&self, ty: &IRType) -> String {
        match ty {
            IRType::Void => "void".to_string(),
            IRType::I1 => "i1".to_string(),
            IRType::I8 => "i8".to_string(),
            IRType::I32 => "i32".to_string(),
            IRType::Ptr(_) => "ptr".to_string(),
            IRType::Struct { fields } => {
                if fields.is_empty() {
                    "{ }".to_string()
                } else {
                    let inner = fields
                        .iter()
                        .map(|f| self.format_type(f))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{{ {} }}", inner)
                }
            }
            IRType::Array { elem_type, size } => {
                format!("[{} x {}]", size, self.format_type(elem_type))
            }
        }
    }

    fn format_value(&self, value: &IRValue) -> String {
        match value {
            IRValue::ConstInt { value, .. } => value.to_string(),
            IRValue::ConstNull(_) => "null".to_string(),
            IRValue::Undef(_) => "undef".to_string(),
            IRValue::Local { name, .. } => self.ensure_prefix(name, '%'),
            IRValue::Global { name, .. } => self.ensure_prefix(name, '@'),
            IRValue::Argument { index, name, .. } => {
                if let Some(name) = name {
                    self.ensure_prefix(name, '%')
                } else {
                    format!("%arg{}", index)
                }
            }
            IRValue::InstructionRef { id, .. } => self.ensure_prefix(id, '%'),
        }
    }

    fn format_argument_name(&self, name: &str) -> String {
        self.ensure_prefix(name, '%')
    }

    fn ensure_prefix(&self, name: &str, prefix: char) -> String {
        if name.starts_with(prefix) {
            name.to_string()
        } else {
            format!("{}{}", prefix, name)
        }
    }
}
