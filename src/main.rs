mod frontend;
mod middleend;

use std::env;
use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use frontend::r_lexer::lexer::Lexer;
use frontend::r_parser::parser::Parser;
use std::panic;

use crate::frontend::r_semantic::analyzer::Analyzer;
use crate::middleend::ir::emitter::{compile_and_run_ir, emit_module, validate_with_llvm_as};
use crate::middleend::ir::lower::Lower;

const DEFAULT_RUNTIME_TIMEOUT_SECS: u64 = 10;

fn print_usage() {
    eprintln!(
        "Usage:
    RCompiler-2025 --ast-json   [INPUT] [--out OUTPUT] [--ir-out IR] [--print-ir] [--run] [--stdin-file INPUT]
    RCompiler-2025 --ast-pretty [INPUT] [--out OUTPUT] [--ir-out IR] [--print-ir] [--run] [--stdin-file INPUT]
  RCompiler-2025 --semantic-test [TESTDIR]
  RCompiler-2025 --semantic-test-2 [TESTDIR]
  RCompiler-2025 --test-single SOURCE [--input INPUT] [--output OUTPUT] [--expected-exit CODE] [--expected-compile CODE] [--save-ir-on-fail]
  RCompiler-2025 --test-semantic-single TESTNAME [--suite SUITE] [--save-ir-on-fail]

Notes:
  - If INPUT is omitted, source is read from stdin.
  - One of --ast-json or --ast-pretty must be provided.
  - If --out is omitted, result is printed to stdout.
    - --ir-out writes the generated LLVM IR to the provided path.
    - --print-ir prints the generated LLVM IR to stdout.
    - --run builds and executes the generated program; combine with --stdin-file to feed stdin.
    - --stdin-file supplies stdin when running the compiled program.
  - --semantic-test will run all semantic tests under testcases/semantic-1 by default.
  - --semantic-test-2 will run all semantic tests under testcases/semantic-2 by default.
  - --test-single tests a single source file with optional input/output validation.
    - --input: path to input file for the program
    - --output: path to expected output file
    - --expected-exit: expected program exit code (default: 0)
    - --expected-compile: expected compilation exit code (default: 0)
    - --save-ir-on-fail: save IR to 'failed_single_test_ir/' directory on failure
  - --test-semantic-single tests a single test case from semantic test suites.
    - TESTNAME: name of the test (e.g., 'basic1', 'return2')
    - --suite: test suite name ('semantic-1' or 'semantic-2', default: 'semantic-1')
    - --save-ir-on-fail: save IR to 'failed_single_test_ir/' directory on failure"
    );
}

fn read_source(maybe_path: Option<&str>) -> io::Result<String> {
    match maybe_path {
        Some(path) => fs::read_to_string(path),
        None => {
            let mut buf = String::new();
            io::stdin().read_to_string(&mut buf)?;
            Ok(buf)
        }
    }
}

fn render_ast_json<N: serde::Serialize>(nodes: &N) -> Result<String, String> {
    serde_json::to_string_pretty(nodes).map_err(|e| format!("serialize json: {e}"))
}

fn render_ast_pretty<N: std::fmt::Debug>(nodes: &N) -> String {
    format!("{:#?}", nodes)
}

fn write_output(path: Option<&Path>, content: &str) -> Result<(), String> {
    if let Some(p) = path {
        fs::write(p, content).map_err(|e| format!("write {}: {e}", p.display()))
    } else {
        println!("{content}");
        Ok(())
    }
}

fn run_emit(
    pretty_out: bool,
    src: String,
    out_path: Option<&Path>,
    input_path: Option<&Path>,
    ir_out_path: Option<&Path>,
    print_ir: bool,
    run_program: bool,
    runtime_input: Option<&[u8]>,
) -> i32 {
    let start_time = Instant::now();

    // Lex
    let lex_start = Instant::now();
    let mut lexer = match Lexer::new(src) {
        Ok(lx) => lx,
        Err(e) => {
            eprintln!("lex error: {e}");
            return 1;
        }
    };
    let tokens = match lexer.tokenize() {
        Ok(t) => t,
        Err(e) => {
            eprintln!("lex error: {e}");
            return 1;
        }
    };
    let lex_duration = lex_start.elapsed();

    // Parse
    let parse_start = Instant::now();
    let mut parser = Parser::new(tokens);
    let nodes = match parser.parse() {
        Ok(n) => n,
        Err(e) => {
            eprintln!("parse error: {e}");
            return 1;
        }
    };
    let parse_duration = parse_start.elapsed();

    // Emit
    let emit_start = Instant::now();
    if pretty_out {
        let pretty = render_ast_pretty(&nodes);
        if let Err(e) = write_output(out_path, &pretty) {
            eprintln!("{e}");
            return 1;
        }
    } else {
        match render_ast_json(&nodes) {
            Ok(json) => {
                if let Err(e) = write_output(out_path, &json) {
                    eprintln!("{e}");
                    return 1;
                }
            }
            Err(e) => {
                eprintln!("ast to json failed: {e}");
                return 1;
            }
        }
    }
    let emit_duration = emit_start.elapsed();

    // Analyzing
    let analyze_start = Instant::now();
    let mut analyzer = Analyzer::new();
    if let Err(e) = analyzer.analyse_program(&nodes) {
        eprintln!("semantic error: {e}");
        return 1;
    }
    let analyze_duration = analyze_start.elapsed();

    // Lowering to IR and validating with llvm
    let lower_start = Instant::now();
    let module_name = input_module_name(out_path, pretty_out, input_path);
    let lower = Lower::new(&nodes, &analyzer.type_context);
    let ir_module = match lower.lower_program(&module_name) {
        Ok(module) => module,
        Err(err) => {
            eprintln!("lowering error: {err}");
            return 1;
        }
    };
    let ir_text = emit_module(&ir_module);

    if let Some(ir_path) = ir_out_path {
        if let Err(err) = fs::write(ir_path, &ir_text) {
            eprintln!("failed to write IR to {}: {err}", ir_path.display());
            return 1;
        }
    }

    if print_ir {
        print!("{ir_text}");
    }
    let lower_duration = lower_start.elapsed();

    let llvm_start = Instant::now();
    if let Err(err) = validate_with_llvm_as(&ir_text) {
        eprintln!("LLVM IR validation error: {err}");
        eprintln!("--- begin ir ---\n{ir_text}\n--- end ir ---");
        return 1;
    }
    let llvm_duration = llvm_start.elapsed();

    let mut exec_duration = None;
    let mut program_exit_code = None;

    if run_program {
        let runtime_data = runtime_input.unwrap_or(&[]);
        let exec_start = Instant::now();
        let timeout = Duration::from_secs(DEFAULT_RUNTIME_TIMEOUT_SECS);
        match compile_and_run_ir(&ir_text, runtime_data, timeout) {
            Ok(result) => {
                exec_duration = Some(exec_start.elapsed());
                program_exit_code = Some(result.exit_code);
                print!("{}", result.stdout);
                if !result.stderr.is_empty() {
                    eprintln!("Program stderr:\n{}", result.stderr);
                }
                eprintln!("Program exit code: {}", result.exit_code);
            }
            Err(err) => {
                eprintln!("Failed to execute compiled program: {err}");
                return 1;
            }
        }
    }

    let total_duration = start_time.elapsed();

    eprintln!("Timing information:");
    eprintln!(
        "  Lexing:     {:>8.3}ms",
        lex_duration.as_secs_f64() * 1000.0
    );
    eprintln!(
        "  Parsing:    {:>8.3}ms",
        parse_duration.as_secs_f64() * 1000.0
    );
    eprintln!(
        "  Emitting:   {:>8.3}ms",
        emit_duration.as_secs_f64() * 1000.0
    );
    eprintln!(
        "  Analyzing:  {:>8.3}ms",
        analyze_duration.as_secs_f64() * 1000.0
    );
    eprintln!(
        "  Lowering:   {:>8.3}ms",
        lower_duration.as_secs_f64() * 1000.0
    );
    eprintln!(
        "  LLVM:      {:>8.3}ms",
        llvm_duration.as_secs_f64() * 1000.0
    );
    if let Some(exec_duration) = exec_duration {
        eprintln!(
            "  Execute:   {:>8.3}ms",
            exec_duration.as_secs_f64() * 1000.0
        );
    }
    eprintln!(
        "  Total:      {:>8.3}ms",
        total_duration.as_secs_f64() * 1000.0
    );

    if run_program {
        program_exit_code.unwrap_or(0)
    } else {
        0
    }
}

// Compile only for semantic checking (no AST emission). Returns 0 on success, -1 on failure.
fn compile_semantic(src: &str) -> Result<(), String> {
    compile_to_ir(src).map(|_| ())
}

fn compile_to_ir(src: &str) -> Result<String, String> {
    let result = panic::catch_unwind(|| -> Result<String, String> {
        // Lex
        let mut lexer = Lexer::new(src.to_string()).map_err(|e| e.to_string())?;
        let tokens = lexer.tokenize().map_err(|e| e.to_string())?;
        // Parse
        let mut parser = Parser::new(tokens);
        let nodes = parser.parse().map_err(|e| e.to_string())?;
        // Analyze
        let mut analyzer = Analyzer::new();
        analyzer
            .analyse_program(&nodes)
            .map_err(|e| e.to_string())?;
        // Lower to IR
        let module_name = "semantic_check_module".to_string();
        let lower = Lower::new(&nodes, &analyzer.type_context);
        let ir_module = lower
            .lower_program(&module_name)
            .map_err(|err| err.to_string())?;
        let ir_text = emit_module(&ir_module);
        Ok(ir_text)
    });
    match result {
        Ok(inner) => inner,
        Err(_) => {
            Err("panic during compilation (likely invalid UTF-8 boundary in lexer)".to_string())
        }
    }
}

fn preview_content(s: &str) -> String {
    const LIMIT: usize = 120;
    let mut escaped = s.escape_debug().to_string();
    if escaped.len() > LIMIT {
        escaped.truncate(LIMIT);
        escaped.push_str("...");
    }
    escaped
}

fn runtime_timeout(limit: Option<i64>) -> Duration {
    let secs = match limit {
        Some(v) if v > 0 => v as u64,
        _ => DEFAULT_RUNTIME_TIMEOUT_SECS,
    };
    Duration::from_secs(secs)
}

fn input_module_name(
    out_path: Option<&Path>,
    pretty_out: bool,
    input_path: Option<&Path>,
) -> String {
    if let Some(path) = input_path {
        return path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("module")
            .to_string();
    }

    if let Some(path) = out_path {
        return path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("module")
            .to_string();
    }

    if pretty_out {
        "ast_pretty".to_string()
    } else {
        "ast_json".to_string()
    }
}

fn run_semantic_tests(root: Option<String>) -> i32 {
    let start_time = Instant::now();

    let test_root = root.unwrap_or_else(|| "testcases/semantic-1".to_string());
    let path = Path::new(&test_root);
    if !path.exists() {
        eprintln!("Test root not found: {}", path.display());
        return 1;
    }

    let global_manifest = path.join("global.json");
    if global_manifest.exists() {
        return run_semantic_tests_with_manifest(path, &global_manifest, start_time);
    }

    // Helper to run one case directory
    fn run_case(case_dir: &Path) -> (String, i32, i32, Option<String>, bool) {
        let mut rx_file: Option<PathBuf> = None;
        let mut expected_exit: Option<i32> = None;
        if let Ok(files) = fs::read_dir(case_dir) {
            for f in files.flatten() {
                let p = f.path();
                if p.extension().map(|s| s == "rx").unwrap_or(false) {
                    rx_file = Some(p);
                } else if p
                    .file_name()
                    .map(|n| n == "testcase_info.json")
                    .unwrap_or(false)
                {
                    if let Ok(txt) = fs::read_to_string(&p) {
                        if let Ok(val) = serde_json::from_str::<serde_json::Value>(&txt) {
                            if let Some(v) = val.get("compileexitcode") {
                                expected_exit = v.as_i64().map(|i| i as i32);
                            }
                        }
                    }
                }
            }
        }
        let case_name = case_dir.file_name().unwrap().to_string_lossy().to_string();
        let Some(rx_path) = rx_file else {
            return (
                case_name,
                0,
                -999,
                Some("no rx file found".to_string()),
                false,
            );
        };
        let expected = expected_exit.unwrap_or(0);
        let src = match fs::read_to_string(&rx_path) {
            Ok(s) => s,
            Err(_) => {
                return (
                    case_name,
                    expected,
                    -999,
                    Some("read source failed".to_string()),
                    false,
                );
            }
        };
        let res = compile_semantic(&src);
        let actual_std = if res.is_ok() { 0 } else { -1 };
        let passed = actual_std == expected;
        let error_msg = if passed {
            None
        } else {
            res.err().or_else(|| Some("<unknown error>".to_string()))
        };
        (case_name, expected, actual_std, error_msg, passed)
    }

    // Decide whether path itself is a single case.
    let is_single_case = path.is_dir()
        && fs::read_dir(path)
            .ok()
            .map(|mut it| {
                it.any(|e| {
                    e.ok()
                        .map(|f| f.path().extension().map(|s| s == "rx").unwrap_or(false))
                        .unwrap_or(false)
                })
            })
            .unwrap_or(false)
        && fs::read_dir(path)
            .ok()
            .map(|mut it| {
                it.any(|e| {
                    e.ok()
                        .map(|f| {
                            f.path()
                                .file_name()
                                .map(|n| n == "testcase_info.json")
                                .unwrap_or(false)
                        })
                        .unwrap_or(false)
                })
            })
            .unwrap_or(false);

    let mut total = 0usize;
    let mut passed = 0usize;
    let mut failed_cases: Vec<(String, i32, i32, String)> = Vec::new();
    let mut passed_cases: Vec<String> = Vec::new();

    if is_single_case {
        total = 1;
        let (name, expected, actual, error_msg, success) = run_case(path);
        if success {
            passed = 1;
            passed_cases.push(name);
        } else {
            failed_cases.push((
                name,
                expected,
                actual,
                error_msg.unwrap_or_else(|| "<unknown error>".to_string()),
            ));
        }
    } else {
        let entries = match fs::read_dir(path) {
            Ok(e) => e,
            Err(e) => {
                eprintln!("Cannot read test root {}: {e}", path.display());
                return 1;
            }
        };
        for entry in entries.flatten() {
            let md = match entry.metadata() {
                Ok(m) => m,
                Err(_) => continue,
            };
            if !md.is_dir() {
                continue;
            }
            total += 1;
            let (name, expected, actual, error_msg, success) = run_case(&entry.path());
            if success {
                passed += 1;
                passed_cases.push(name);
            } else {
                failed_cases.push((
                    name,
                    expected,
                    actual,
                    error_msg.unwrap_or_else(|| "<unknown error>".to_string()),
                ));
            }
        }
    }

    println!("Semantic tests: {passed}/{total} passed");

    if !passed_cases.is_empty() {
        println!("Passed cases:");
        for name in &passed_cases {
            println!("  ✓ {name}");
        }
        println!();
    }

    if !failed_cases.is_empty() {
        println!("Failed cases:");
        for (name, exp, act, msg) in &failed_cases {
            println!("  ✗ {name}: expected {exp}, got {act}\n    error: {msg}");
        }
        let total_duration = start_time.elapsed();
        eprintln!(
            "Total test time: {:.3}ms",
            total_duration.as_secs_f64() * 1000.0
        );
        return 1;
    }
    let total_duration = start_time.elapsed();
    eprintln!(
        "Total test time: {:.3}ms",
        total_duration.as_secs_f64() * 1000.0
    );
    0
}

fn run_semantic_tests_with_manifest(path: &Path, manifest_path: &Path, start_time: Instant) -> i32 {
    let manifest_txt = match fs::read_to_string(manifest_path) {
        Ok(txt) => txt,
        Err(e) => {
            eprintln!("Failed to read manifest {}: {e}", manifest_path.display());
            return 1;
        }
    };

    let entries: Vec<serde_json::Value> = match serde_json::from_str(&manifest_txt) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("Failed to parse manifest {}: {e}", manifest_path.display());
            return 1;
        }
    };

    // Create directory for failed test IRs
    let failed_ir_dir = PathBuf::from("failed_test_ir");
    if let Err(e) = fs::create_dir_all(&failed_ir_dir) {
        eprintln!("Warning: failed to create failed_test_ir directory: {e}");
    }

    let mut total = 0usize;
    let mut passed = 0usize;
    let mut failed_cases: Vec<(String, i32, i32, String)> = Vec::new();
    let mut passed_cases: Vec<String> = Vec::new();

    for entry in entries {
        let active = entry
            .get("active")
            .and_then(|v| v.as_bool())
            .unwrap_or(true);
        if !active {
            continue;
        }

        total += 1;

        let name = entry
            .get("name")
            .and_then(|v| v.as_str())
            .unwrap_or("<unnamed>")
            .to_string();
        let expected_compile = entry
            .get("compileexitcode")
            .and_then(|v| v.as_i64())
            .map(|v| v as i32)
            .unwrap_or(0);
        let expected_exit = entry
            .get("exitcode")
            .and_then(|v| v.as_i64())
            .map(|v| v as i32)
            .unwrap_or(0);
        let runtime_limit = entry.get("runtimelimit").and_then(|v| v.as_i64());
        let source_rel = entry
            .get("source")
            .and_then(|v| v.as_array())
            .and_then(|arr| arr.get(0))
            .and_then(|v| v.as_str())
            .map(|s| s.to_string());
        let input_rel = entry
            .get("input")
            .and_then(|v| v.as_array())
            .and_then(|arr| arr.get(0))
            .and_then(|v| v.as_str())
            .map(|s| s.to_string());
        let output_rel = entry
            .get("output")
            .and_then(|v| v.as_array())
            .and_then(|arr| arr.get(0))
            .and_then(|v| v.as_str())
            .map(|s| s.to_string());

        let Some(source_rel) = source_rel else {
            failed_cases.push((
                name.clone(),
                expected_compile,
                -999,
                "manifest missing source path".to_string(),
            ));
            continue;
        };

        let source_path = path.join(source_rel);
        let src = match fs::read_to_string(&source_path) {
            Ok(s) => s,
            Err(e) => {
                failed_cases.push((
                    name.clone(),
                    expected_compile,
                    -999,
                    format!("failed to read {}: {e}", source_path.display()),
                ));
                continue;
            }
        };

        let ir_text = match compile_to_ir(&src) {
            Ok(ir) => ir,
            Err(err) => {
                let actual = -1;
                if expected_compile == actual {
                    passed += 1;
                    passed_cases.push(name.clone());
                } else {
                    failed_cases.push((name.clone(), expected_compile, actual, err));
                }
                continue;
            }
        };

        if expected_compile != 0 {
            // Save IR for unexpected successful compilation
            let ir_file_path = failed_ir_dir.join(format!("{}_unexpected_success.ll", name));
            if let Err(e) = fs::write(&ir_file_path, &ir_text) {
                eprintln!("Warning: failed to save IR for {}: {e}", name);
            }
            failed_cases.push((
                name.clone(),
                expected_compile,
                0,
                format!("expected compile exit code {}, got 0", expected_compile),
            ));
            continue;
        }

        if let Err(err) = validate_with_llvm_as(&ir_text) {
            // Save IR for LLVM validation failure
            let ir_file_path = failed_ir_dir.join(format!("{}_llvm_validation_failed.ll", name));
            if let Err(e) = fs::write(&ir_file_path, &ir_text) {
                eprintln!("Warning: failed to save IR for {}: {e}", name);
            }
            failed_cases.push((
                name.clone(),
                expected_compile,
                0,
                format!("LLVM validation failed: {err}"),
            ));
            continue;
        }

        let input_bytes = match input_rel {
            Some(rel) => {
                let input_path = path.join(&rel);
                match fs::read(&input_path) {
                    Ok(bytes) => bytes,
                    Err(e) => {
                        failed_cases.push((
                            name.clone(),
                            expected_compile,
                            0,
                            format!("failed to read {}: {e}", input_path.display()),
                        ));
                        continue;
                    }
                }
            }
            None => Vec::new(),
        };

        let timeout = runtime_timeout(runtime_limit);
        let exec_result = match compile_and_run_ir(&ir_text, &input_bytes, timeout) {
            Ok(res) => res,
            Err(err) => {
                // Save IR for execution failure
                let ir_file_path = failed_ir_dir.join(format!("{}_execution_failed.ll", name));
                if let Err(e) = fs::write(&ir_file_path, &ir_text) {
                    eprintln!("Warning: failed to save IR for {}: {e}", name);
                }
                failed_cases.push((
                    name.clone(),
                    expected_compile,
                    0,
                    format!("execution failed: {err}"),
                ));
                continue;
            }
        };

        if exec_result.exit_code != expected_exit {
            // Save IR for exit code mismatch
            let ir_file_path = failed_ir_dir.join(format!("{}_exit_code_mismatch.ll", name));
            if let Err(e) = fs::write(&ir_file_path, &ir_text) {
                eprintln!("Warning: failed to save IR for {}: {e}", name);
            }
            failed_cases.push((
                name.clone(),
                expected_compile,
                0,
                format!(
                    "runtime exit code mismatch: expected {}, got {}",
                    expected_exit, exec_result.exit_code
                ),
            ));
            continue;
        }

        let expected_stdout = match output_rel {
            Some(rel) => {
                let output_path = path.join(&rel);
                match fs::read_to_string(&output_path) {
                    Ok(content) => content,
                    Err(e) => {
                        failed_cases.push((
                            name.clone(),
                            expected_compile,
                            0,
                            format!("failed to read {}: {e}", output_path.display()),
                        ));
                        continue;
                    }
                }
            }
            None => String::new(),
        };

        if exec_result.stdout != expected_stdout {
            // Save IR for stdout mismatch
            let ir_file_path = failed_ir_dir.join(format!("{}_stdout_mismatch.ll", name));
            if let Err(e) = fs::write(&ir_file_path, &ir_text) {
                eprintln!("Warning: failed to save IR for {}: {e}", name);
            }
            failed_cases.push((
                name.clone(),
                expected_compile,
                0,
                format!(
                    "runtime stdout mismatch:\n      expected: \"{}\"\n      actual: \"{}\"",
                    preview_content(&expected_stdout),
                    preview_content(&exec_result.stdout)
                ),
            ));
            continue;
        }

        if !exec_result.stderr.is_empty() {
            eprintln!("[{}] program stderr:\n{}", name, exec_result.stderr);
        }

        passed += 1;
        passed_cases.push(name);
    }

    println!("Semantic tests: {passed}/{total} passed");

    if !passed_cases.is_empty() {
        println!("Passed cases:");
        for name in &passed_cases {
            println!("  ✓ {name}");
        }
        println!();
    }

    if !failed_cases.is_empty() {
        println!("Failed cases:");
        for (name, exp, act, msg) in &failed_cases {
            println!("  ✗ {name}: expected {exp}, got {act}\n    error: {msg}");
        }
        let total_duration = start_time.elapsed();
        eprintln!(
            "Total test time: {:.3}ms",
            total_duration.as_secs_f64() * 1000.0
        );
        return 1;
    }

    let total_duration = start_time.elapsed();
    eprintln!(
        "Total test time: {:.3}ms",
        total_duration.as_secs_f64() * 1000.0
    );
    0
}

fn run_single_file_test(
    source_path: &Path,
    input_path: Option<&Path>,
    output_path: Option<&Path>,
    expected_exit: i32,
    expected_compile: i32,
    save_ir_on_fail: bool,
) -> i32 {
    let start_time = Instant::now();

    let test_name = source_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("unnamed");

    println!("Testing: {}", source_path.display());
    println!("  Expected compile exit: {}", expected_compile);
    println!("  Expected runtime exit: {}", expected_exit);

    // Read source file
    let src = match fs::read_to_string(source_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("✗ Failed to read source file: {e}");
            return 1;
        }
    };

    // Compile to IR
    let ir_text = match compile_to_ir(&src) {
        Ok(ir) => ir,
        Err(err) => {
            let actual_compile = -1;
            if expected_compile == actual_compile {
                println!("✓ Test passed: compilation failed as expected");
                println!("  Error: {}", err);
                let duration = start_time.elapsed();
                eprintln!("Test time: {:.3}ms", duration.as_secs_f64() * 1000.0);
                return 0;
            } else {
                eprintln!("✗ Test failed: compilation error");
                eprintln!("  Expected compile exit: {}", expected_compile);
                eprintln!("  Actual compile exit: {}", actual_compile);
                eprintln!("  Error: {}", err);
                let duration = start_time.elapsed();
                eprintln!("Test time: {:.3}ms", duration.as_secs_f64() * 1000.0);
                return 1;
            }
        }
    };

    // Check if compilation should have failed
    if expected_compile != 0 {
        eprintln!("✗ Test failed: expected compilation to fail");
        eprintln!("  Expected compile exit: {}", expected_compile);
        eprintln!("  Actual compile exit: 0");
        if save_ir_on_fail {
            save_failed_ir(&ir_text, test_name, "unexpected_success");
        }
        let duration = start_time.elapsed();
        eprintln!("Test time: {:.3}ms", duration.as_secs_f64() * 1000.0);
        return 1;
    }

    println!("✓ Compilation succeeded");

    // Validate with LLVM
    if let Err(err) = validate_with_llvm_as(&ir_text) {
        eprintln!("✗ Test failed: LLVM validation error");
        eprintln!("  Error: {}", err);
        if save_ir_on_fail {
            save_failed_ir(&ir_text, test_name, "llvm_validation_failed");
        }
        let duration = start_time.elapsed();
        eprintln!("Test time: {:.3}ms", duration.as_secs_f64() * 1000.0);
        return 1;
    }

    println!("✓ LLVM validation passed");

    // Read input if provided
    let input_bytes = match input_path {
        Some(path) => match fs::read(path) {
            Ok(bytes) => bytes,
            Err(e) => {
                eprintln!("✗ Failed to read input file: {e}");
                if save_ir_on_fail {
                    save_failed_ir(&ir_text, test_name, "input_read_failed");
                }
                let duration = start_time.elapsed();
                eprintln!("Test time: {:.3}ms", duration.as_secs_f64() * 1000.0);
                return 1;
            }
        },
        None => Vec::new(),
    };

    // Execute program
    let timeout = Duration::from_secs(DEFAULT_RUNTIME_TIMEOUT_SECS);
    let exec_result = match compile_and_run_ir(&ir_text, &input_bytes, timeout) {
        Ok(res) => res,
        Err(err) => {
            eprintln!("✗ Test failed: execution error");
            eprintln!("  Error: {}", err);
            if save_ir_on_fail {
                save_failed_ir(&ir_text, test_name, "execution_failed");
            }
            let duration = start_time.elapsed();
            eprintln!("Test time: {:.3}ms", duration.as_secs_f64() * 1000.0);
            return 1;
        }
    };

    println!("✓ Execution completed");
    println!("  Exit code: {}", exec_result.exit_code);

    // Check exit code
    if exec_result.exit_code != expected_exit {
        eprintln!("✗ Test failed: exit code mismatch");
        eprintln!("  Expected: {}", expected_exit);
        eprintln!("  Actual: {}", exec_result.exit_code);
        if save_ir_on_fail {
            save_failed_ir(&ir_text, test_name, "exit_code_mismatch");
        }
        if !exec_result.stdout.is_empty() {
            println!("  Stdout: {}", preview_content(&exec_result.stdout));
        }
        if !exec_result.stderr.is_empty() {
            println!("  Stderr: {}", preview_content(&exec_result.stderr));
        }
        let duration = start_time.elapsed();
        eprintln!("Test time: {:.3}ms", duration.as_secs_f64() * 1000.0);
        return 1;
    }

    // Check output if provided
    if let Some(out_path) = output_path {
        let expected_output = match fs::read_to_string(out_path) {
            Ok(content) => content,
            Err(e) => {
                eprintln!("✗ Failed to read expected output file: {e}");
                if save_ir_on_fail {
                    save_failed_ir(&ir_text, test_name, "output_read_failed");
                }
                let duration = start_time.elapsed();
                eprintln!("Test time: {:.3}ms", duration.as_secs_f64() * 1000.0);
                return 1;
            }
        };

        if exec_result.stdout != expected_output {
            eprintln!("✗ Test failed: output mismatch");
            eprintln!("  Expected: \"{}\"", preview_content(&expected_output));
            eprintln!("  Actual: \"{}\"", preview_content(&exec_result.stdout));
            if save_ir_on_fail {
                save_failed_ir(&ir_text, test_name, "stdout_mismatch");
            }
            let duration = start_time.elapsed();
            eprintln!("Test time: {:.3}ms", duration.as_secs_f64() * 1000.0);
            return 1;
        }

        println!("✓ Output matches expected");
    } else {
        println!("  Stdout: {}", preview_content(&exec_result.stdout));
        if !exec_result.stderr.is_empty() {
            println!("  Stderr: {}", preview_content(&exec_result.stderr));
        }
    }

    println!("✓ Test passed!");
    let duration = start_time.elapsed();
    eprintln!("Test time: {:.3}ms", duration.as_secs_f64() * 1000.0);
    0
}

fn save_failed_ir(ir_text: &str, test_name: &str, reason: &str) {
    let failed_ir_dir = PathBuf::from("failed_single_test_ir");
    if let Err(e) = fs::create_dir_all(&failed_ir_dir) {
        eprintln!("Warning: failed to create failed_single_test_ir directory: {e}");
        return;
    }

    let ir_file_path = failed_ir_dir.join(format!("{}_{}.ll", test_name, reason));
    if let Err(e) = fs::write(&ir_file_path, ir_text) {
        eprintln!(
            "Warning: failed to save IR to {}: {e}",
            ir_file_path.display()
        );
    } else {
        println!("  IR saved to: {}", ir_file_path.display());
    }
}

fn run_semantic_single_test(test_name: &str, suite_name: &str, save_ir_on_fail: bool) -> i32 {
    let start_time = Instant::now();

    // Determine paths based on suite
    let suite_dir = PathBuf::from("testcases").join(suite_name);
    let manifest_path = suite_dir.join("global.json");

    println!("Testing: {} (from {})", test_name, suite_name);

    // Read and parse manifest
    let manifest_txt = match fs::read_to_string(&manifest_path) {
        Ok(txt) => txt,
        Err(e) => {
            eprintln!(
                "✗ Failed to read manifest {}: {}",
                manifest_path.display(),
                e
            );
            return 1;
        }
    };

    let entries: Vec<serde_json::Value> = match serde_json::from_str(&manifest_txt) {
        Ok(v) => v,
        Err(e) => {
            eprintln!(
                "✗ Failed to parse manifest {}: {}",
                manifest_path.display(),
                e
            );
            return 1;
        }
    };

    // Find the test entry
    let test_entry = entries.iter().find(|entry| {
        entry
            .get("name")
            .and_then(|v| v.as_str())
            .map(|n| n == test_name)
            .unwrap_or(false)
    });

    let Some(entry) = test_entry else {
        eprintln!("✗ Test '{}' not found in manifest", test_name);
        eprintln!("Available tests in {}:", suite_name);
        for e in entries.iter().take(10) {
            if let Some(name) = e.get("name").and_then(|v| v.as_str()) {
                eprintln!("  - {}", name);
            }
        }
        if entries.len() > 10 {
            eprintln!("  ... and {} more", entries.len() - 10);
        }
        return 1;
    };

    // Extract test parameters
    let active = entry
        .get("active")
        .and_then(|v| v.as_bool())
        .unwrap_or(true);

    if !active {
        println!("⚠ Test is marked as inactive");
        return 0;
    }

    let expected_compile = entry
        .get("compileexitcode")
        .and_then(|v| v.as_i64())
        .map(|v| v as i32)
        .unwrap_or(0);
    let expected_exit = entry
        .get("exitcode")
        .and_then(|v| v.as_i64())
        .map(|v| v as i32)
        .unwrap_or(0);
    let runtime_limit = entry.get("runtimelimit").and_then(|v| v.as_i64());

    let source_rel = entry
        .get("source")
        .and_then(|v| v.as_array())
        .and_then(|arr| arr.get(0))
        .and_then(|v| v.as_str());
    let input_rel = entry
        .get("input")
        .and_then(|v| v.as_array())
        .and_then(|arr| arr.get(0))
        .and_then(|v| v.as_str());
    let output_rel = entry
        .get("output")
        .and_then(|v| v.as_array())
        .and_then(|arr| arr.get(0))
        .and_then(|v| v.as_str());

    let Some(source_rel) = source_rel else {
        eprintln!("✗ Manifest missing source path");
        return 1;
    };

    // Read source file
    let source_path = suite_dir.join(source_rel);
    println!("  Source: {}", source_path.display());

    let src = match fs::read_to_string(&source_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("✗ Failed to read {}: {}", source_path.display(), e);
            return 1;
        }
    };

    // Compile to IR
    println!("  Expected compile exit code: {}", expected_compile);
    println!("  Expected runtime exit code: {}", expected_exit);

    let ir_text = match compile_to_ir(&src) {
        Ok(ir) => {
            if expected_compile != 0 {
                eprintln!(
                    "✗ Expected compilation to fail with exit code {}, but it succeeded",
                    expected_compile
                );
                if save_ir_on_fail {
                    save_failed_ir(&ir, test_name, "unexpected_success");
                }
                return 1;
            }
            println!("✓ Compilation succeeded");
            ir
        }
        Err(err) => {
            let actual = -1;
            if expected_compile == actual {
                println!("✓ Compilation failed as expected");
                println!("  Error: {}", err);
                let duration = start_time.elapsed();
                eprintln!("Test time: {:.3}ms", duration.as_secs_f64() * 1000.0);
                return 0;
            } else {
                eprintln!("✗ Compilation failed unexpectedly");
                eprintln!("  Expected compile exit code: {}", expected_compile);
                eprintln!("  Actual: -1");
                eprintln!("  Error: {}", err);
                return 1;
            }
        }
    };

    // Validate with LLVM
    if let Err(err) = validate_with_llvm_as(&ir_text) {
        eprintln!("✗ LLVM validation failed: {}", err);
        if save_ir_on_fail {
            save_failed_ir(&ir_text, test_name, "llvm_validation_failed");
        }
        return 1;
    }
    println!("✓ LLVM validation passed");

    // Read input if specified
    let input_bytes = match input_rel {
        Some(rel) => {
            let input_path = suite_dir.join(rel);
            println!("  Input: {}", input_path.display());
            match fs::read(&input_path) {
                Ok(bytes) => bytes,
                Err(e) => {
                    eprintln!("✗ Failed to read {}: {}", input_path.display(), e);
                    return 1;
                }
            }
        }
        None => {
            println!("  Input: <none>");
            Vec::new()
        }
    };

    // Execute
    let timeout = runtime_timeout(runtime_limit);
    let exec_result = match compile_and_run_ir(&ir_text, &input_bytes, timeout) {
        Ok(res) => res,
        Err(err) => {
            eprintln!("✗ Execution failed: {}", err);
            if save_ir_on_fail {
                save_failed_ir(&ir_text, test_name, "execution_failed");
            }
            return 1;
        }
    };

    println!(
        "✓ Execution completed (Exit code: {})",
        exec_result.exit_code
    );

    // Check exit code
    if exec_result.exit_code != expected_exit {
        eprintln!("✗ Exit code mismatch");
        eprintln!("  Expected: {}", expected_exit);
        eprintln!("  Actual: {}", exec_result.exit_code);
        if save_ir_on_fail {
            save_failed_ir(&ir_text, test_name, "exit_code_mismatch");
        }
        return 1;
    }

    // Check output if specified
    if let Some(output_rel) = output_rel {
        let output_path = suite_dir.join(output_rel);
        println!("  Expected output: {}", output_path.display());

        let expected_output = match fs::read(&output_path) {
            Ok(bytes) => bytes,
            Err(e) => {
                eprintln!("✗ Failed to read {}: {}", output_path.display(), e);
                return 1;
            }
        };

        let expected_str = String::from_utf8_lossy(&expected_output);
        if exec_result.stdout != expected_str {
            eprintln!("✗ Output mismatch");
            eprintln!("  Expected: {}", preview_content(&expected_str));
            eprintln!("  Actual: {}", preview_content(&exec_result.stdout));
            if save_ir_on_fail {
                save_failed_ir(&ir_text, test_name, "stdout_mismatch");
            }
            return 1;
        }
        println!("✓ Output matches");
    } else {
        println!("  Actual stdout: {}", preview_content(&exec_result.stdout));
        if !exec_result.stderr.is_empty() {
            println!("  Actual stderr: {}", preview_content(&exec_result.stderr));
        }
    }

    println!("✓ Test passed!");
    let duration = start_time.elapsed();
    eprintln!("Test time: {:.3}ms", duration.as_secs_f64() * 1000.0);
    0
}

fn main() {
    let overall_start = Instant::now();

    let mut args = env::args().skip(1);
    let Some(flag) = args.next() else {
        print_usage();
        return;
    };

    if flag == "--semantic-test" {
        let maybe_dir = args.next();
        let code = run_semantic_tests(maybe_dir);
        let overall_duration = overall_start.elapsed();
        eprintln!(
            "Overall execution time: {:.3}ms",
            overall_duration.as_secs_f64() * 1000.0
        );
        if code != 0 { /* failure already reported */ }
        return;
    }

    if flag == "--semantic-test-2" {
        let maybe_dir = args
            .next()
            .or_else(|| Some("testcases/semantic-2".to_string()));
        let code = run_semantic_tests(maybe_dir);
        let overall_duration = overall_start.elapsed();
        eprintln!(
            "Overall execution time: {:.3}ms",
            overall_duration.as_secs_f64() * 1000.0
        );
        if code != 0 { /* failure already reported */ }
        return;
    }

    if flag == "--test-semantic-single" {
        let Some(test_name) = args.next() else {
            eprintln!("--test-semantic-single requires a test name");
            print_usage();
            return;
        };

        let mut suite_name = "semantic-1".to_string();
        let mut save_ir_on_fail = false;

        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--suite" => {
                    let Some(suite) = args.next() else {
                        eprintln!("--suite requires a suite name (semantic-1 or semantic-2)");
                        return;
                    };
                    if suite != "semantic-1" && suite != "semantic-2" {
                        eprintln!(
                            "Invalid suite name: {}. Must be 'semantic-1' or 'semantic-2'",
                            suite
                        );
                        return;
                    }
                    suite_name = suite;
                }
                "--save-ir-on-fail" => {
                    save_ir_on_fail = true;
                }
                _ => {
                    eprintln!("Unknown option for --test-semantic-single: {}", arg);
                    print_usage();
                    return;
                }
            }
        }

        let code = run_semantic_single_test(&test_name, &suite_name, save_ir_on_fail);
        let overall_duration = overall_start.elapsed();
        eprintln!(
            "Overall execution time: {:.3}ms",
            overall_duration.as_secs_f64() * 1000.0
        );
        if code != 0 { /* failure already reported */ }
        return;
    }

    if flag == "--test-single" {
        let Some(source_path_str) = args.next() else {
            eprintln!("--test-single requires a source file path");
            print_usage();
            return;
        };
        let source_path = PathBuf::from(source_path_str);

        let mut input_path: Option<PathBuf> = None;
        let mut output_path: Option<PathBuf> = None;
        let mut expected_exit: i32 = 0;
        let mut expected_compile: i32 = 0;
        let mut save_ir_on_fail = false;

        while let Some(arg) = args.next() {
            match arg.as_str() {
                "--input" => {
                    let Some(p) = args.next() else {
                        eprintln!("--input requires a path");
                        return;
                    };
                    input_path = Some(PathBuf::from(p));
                }
                "--output" => {
                    let Some(p) = args.next() else {
                        eprintln!("--output requires a path");
                        return;
                    };
                    output_path = Some(PathBuf::from(p));
                }
                "--expected-exit" => {
                    let Some(code_str) = args.next() else {
                        eprintln!("--expected-exit requires an exit code");
                        return;
                    };
                    expected_exit = match code_str.parse() {
                        Ok(code) => code,
                        Err(_) => {
                            eprintln!("--expected-exit requires a valid integer");
                            return;
                        }
                    };
                }
                "--expected-compile" => {
                    let Some(code_str) = args.next() else {
                        eprintln!("--expected-compile requires an exit code");
                        return;
                    };
                    expected_compile = match code_str.parse() {
                        Ok(code) => code,
                        Err(_) => {
                            eprintln!("--expected-compile requires a valid integer");
                            return;
                        }
                    };
                }
                "--save-ir-on-fail" => {
                    save_ir_on_fail = true;
                }
                _ => {
                    eprintln!("Unknown option for --test-single: {}", arg);
                    print_usage();
                    return;
                }
            }
        }

        let code = run_single_file_test(
            &source_path,
            input_path.as_deref(),
            output_path.as_deref(),
            expected_exit,
            expected_compile,
            save_ir_on_fail,
        );
        let overall_duration = overall_start.elapsed();
        eprintln!(
            "Overall execution time: {:.3}ms",
            overall_duration.as_secs_f64() * 1000.0
        );
        if code != 0 { /* failure already reported */ }
        return;
    }

    let pretty_flag = match flag.as_str() {
        "--ast-pretty" => true,
        "--ast-json" => false,
        other => {
            eprintln!("Unknown flag: {other}");
            print_usage();
            return;
        }
    };

    // 解析位置参数 INPUT 与可选 --out OUTPUT
    let mut input_path: Option<PathBuf> = None;
    let mut out_path: Option<PathBuf> = None;
    let mut ir_out_path: Option<PathBuf> = None;
    let mut print_ir = false;
    let mut run_program = false;
    let mut stdin_path: Option<PathBuf> = None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--out" => {
                let Some(p) = args.next() else {
                    eprintln!("--out requires a path");
                    return;
                };
                out_path = Some(PathBuf::from(p));
            }
            "--ir-out" => {
                let Some(p) = args.next() else {
                    eprintln!("--ir-out requires a path");
                    return;
                };
                ir_out_path = Some(PathBuf::from(p));
            }
            "--print-ir" => {
                print_ir = true;
            }
            "--run" => {
                run_program = true;
            }
            "--stdin-file" => {
                let Some(p) = args.next() else {
                    eprintln!("--stdin-file requires a path");
                    return;
                };
                stdin_path = Some(PathBuf::from(p));
            }
            _ if arg.starts_with("--") => {
                eprintln!("Unknown option: {arg}");
                print_usage();
                return;
            }
            _ => {
                if input_path.is_none() {
                    input_path = Some(PathBuf::from(arg));
                } else {
                    eprintln!("Too many positional arguments");
                    print_usage();
                    return;
                }
            }
        }
    }

    let src = match read_source(input_path.as_deref().map(|p| p.to_str().unwrap())) {
        Ok(s) => s,
        Err(e) => {
            if let Some(p) = &input_path {
                eprintln!("failed to read {}: {e}", p.display());
            } else {
                eprintln!("failed to read input: {e}");
            }
            return;
        }
    };

    let runtime_input_data = match stdin_path {
        Some(path) => match fs::read(&path) {
            Ok(data) => Some(data),
            Err(e) => {
                eprintln!("failed to read {}: {e}", path.display());
                return;
            }
        },
        None => None,
    };

    if run_program && runtime_input_data.is_none() && input_path.is_none() {
        eprintln!(
            "Warning: running without --stdin-file after reading source from stdin; program stdin will be empty."
        );
    }

    let code = run_emit(
        pretty_flag,
        src,
        out_path.as_deref(),
        input_path.as_deref(),
        ir_out_path.as_deref(),
        print_ir,
        run_program,
        runtime_input_data.as_deref(),
    );
    let overall_duration = overall_start.elapsed();
    eprintln!(
        "Overall execution time: {:.3}ms",
        overall_duration.as_secs_f64() * 1000.0
    );
    if code != 0 {
        // non-zero exit code path (no process::exit to preserve Drops)
    }
}
