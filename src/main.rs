mod frontend;
mod middleend;

use std::env;
use std::fs;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use frontend::r_lexer::lexer::Lexer;
use frontend::r_parser::parser::Parser;
use std::panic::{self, AssertUnwindSafe};

use crate::frontend::r_semantic::analyzer::Analyzer;
use crate::middleend::ir::emitter::{compile_and_run_ir, emit_module, validate_with_llvm_as};
use crate::middleend::ir::lower::Lower;

fn print_usage() {
    eprintln!(
        "Usage:
  RCompiler-2025 --ast-json  [INPUT] [--out OUTPUT]
  RCompiler-2025 --ast-pretty [INPUT] [--out OUTPUT]
  RCompiler-2025 --semantic-test [TESTDIR]
  RCompiler-2025 --ir-test [TESTDIR]
  RCompiler-2025 --playground

Notes:
  - If INPUT is omitted, source is read from stdin.
  - One of --ast-json or --ast-pretty must be provided.
  - If --out is omitted, result is printed to stdout.
  - --semantic-test will run all semantic tests under testcases/semantic-1 by default.
  - --ir-test will run all IR tests under testcases/IR-1 by default (pass a custom path to override).
  - --playground compiles and runs playground/main.rx with input from playground/in, output to playground/out."
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
    format!("{nodes:#?}")
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
    silent: bool,
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
    if !silent {
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
    let lower_duration = lower_start.elapsed();

    let llvm_start = Instant::now();
    if let Err(err) = validate_with_llvm_as(&ir_text) {
        eprintln!("LLVM IR validation error: {err}");
        eprintln!("--- begin ir ---\n{ir_text}\n--- end ir ---");
        return 1;
    }
    let llvm_duration = llvm_start.elapsed();
    let total_duration = start_time.elapsed();

    if !silent {
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
        eprintln!(
            "  Total:      {:>8.3}ms",
            total_duration.as_secs_f64() * 1000.0
        );
    }

    0
}

// Compile only for semantic checking (no AST emission). Returns 0 on success, -1 on failure.
fn compile_semantic(src: &str) -> Result<(), String> {
    let result = panic::catch_unwind(AssertUnwindSafe(|| -> Result<(), String> {
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
        Ok(())
    }));
    match result {
        Ok(inner) => inner,
        Err(_) => {
            Err("panic during compilation (likely invalid UTF-8 boundary in lexer)".to_string())
        }
    }
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

fn run_compilation_tests<F>(
    root: Option<String>,
    default_root: &str,
    label: &str,
    compile: F,
) -> i32
where
    F: Fn(&str) -> Result<(), String>,
{
    let start_time = Instant::now();

    let test_root = root.unwrap_or_else(|| default_root.to_string());
    let path = Path::new(&test_root);
    if !path.exists() {
        eprintln!("Test root not found: {}", path.display());
        return 1;
    }

    let global_manifest = path.join("global.json");
    if global_manifest.exists() {
        return run_compilation_tests_with_manifest(
            path,
            &global_manifest,
            start_time,
            label,
            &compile,
        );
    }

    fn run_case<F>(case_dir: &Path, compile: &F) -> (String, i32, i32, Option<String>, bool)
    where
        F: Fn(&str) -> Result<(), String>,
    {
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
        let res = compile(&src);
        let actual_std = if res.is_ok() { 0 } else { -1 };
        let passed = actual_std == expected;
        let error_msg = if passed {
            None
        } else {
            res.err().or_else(|| Some("<unknown error>".to_string()))
        };
        (case_name, expected, actual_std, error_msg, passed)
    }

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
        let (name, expected, actual, error_msg, success) = run_case(path, &compile);
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
            let (name, expected, actual, error_msg, success) = run_case(&entry.path(), &compile);
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

    println!("{label} tests: {passed}/{total} passed");

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

fn run_compilation_tests_with_manifest<F>(
    path: &Path,
    manifest_path: &Path,
    start_time: Instant,
    label: &str,
    compile: &F,
) -> i32
where
    F: Fn(&str) -> Result<(), String>,
{
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
        let expected = entry
            .get("compileexitcode")
            .and_then(|v| v.as_i64())
            .map(|v| v as i32)
            .unwrap_or(0);
        let source_rel = entry
            .get("source")
            .and_then(|v| v.as_array())
            .and_then(|arr| arr.first())
            .and_then(|v| v.as_str())
            .map(|s| s.to_string());

        let Some(source_rel) = source_rel else {
            failed_cases.push((
                name.clone(),
                expected,
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
                    expected,
                    -999,
                    format!("failed to read {}: {e}", source_path.display()),
                ));
                continue;
            }
        };

        let compile_result = compile(&src);
        let actual = if compile_result.is_ok() { 0 } else { -1 };

        if actual == expected {
            passed += 1;
            passed_cases.push(name);
        } else {
            let error_msg = match compile_result {
                Ok(_) => format!("expected {expected}, got {actual}"),
                Err(err) => err,
            };
            failed_cases.push((name, expected, actual, error_msg));
        }
    }

    println!("{label} tests: {passed}/{total} passed");

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

fn run_semantic_tests(root: Option<String>) -> i32 {
    run_compilation_tests(root, "testcases/semantic-1", "Semantic", compile_semantic)
}

fn run_playground() -> i32 {
    let playground_dir = Path::new("playground");
    let source_path = playground_dir.join("main.rx");
    let input_path = playground_dir.join("in");
    let output_path = playground_dir.join("out");
    let ir_output_path = playground_dir.join("play.ll");

    // Read source code
    let src = match fs::read_to_string(&source_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Failed to read {}: {e}", source_path.display());
            return 1;
        }
    };

    println!("Compiling {}...", source_path.display());

    // Compile to IR
    let ir_text = match compile_source_to_ir(&src, &source_path) {
        Ok(ir) => ir,
        Err(e) => {
            eprintln!("Compilation failed: {e}");
            return 1;
        }
    };

    println!("Compilation successful!");

    if let Err(e) = fs::write(&ir_output_path, &ir_text) {
        eprintln!("Failed to write IR to {}: {e}", ir_output_path.display());
        std::process::exit(1);
    }

    println!("IR written to {}", ir_output_path.display());

    // Read input file (if exists)
    let stdin_data = match fs::read(&input_path) {
        Ok(data) => {
            println!("Reading input from {}...", input_path.display());
            data
        }
        Err(_) => {
            println!("No input file found, using empty input");
            Vec::new()
        }
    };

    // Run the compiled IR
    println!("Running program...");
    let timeout = Duration::from_secs(30);
    let result = match compile_and_run_ir(&ir_text, &stdin_data, timeout) {
        Ok(res) => res,
        Err(e) => {
            eprintln!("Execution failed: {e}");
            return 1;
        }
    };

    // Write output to file
    if let Err(e) = fs::write(&output_path, &result.stdout) {
        eprintln!("Failed to write output to {}: {e}", output_path.display());
        return 1;
    }

    println!("Output written to {}", output_path.display());
    println!("Exit code: {}", result.exit_code);

    if !result.stderr.is_empty() {
        eprintln!("Stderr:\n{}", result.stderr);
    }

    result.exit_code
}

fn run_ir_tests(root: Option<String>) -> i32 {
    let start_time = Instant::now();

    let test_root = root.unwrap_or_else(|| "testcases/IR-1".to_string());
    let path = Path::new(&test_root);
    if !path.exists() {
        eprintln!("Test root not found: {}", path.display());
        return 1;
    }

    let global_manifest = path.join("global.json");
    if !global_manifest.exists() {
        eprintln!("global.json not found in {}", path.display());
        return 1;
    }

    let manifest_txt = match fs::read_to_string(&global_manifest) {
        Ok(txt) => txt,
        Err(e) => {
            eprintln!("Failed to read manifest {}: {e}", global_manifest.display());
            return 1;
        }
    };

    let entries: Vec<serde_json::Value> = match serde_json::from_str(&manifest_txt) {
        Ok(v) => v,
        Err(e) => {
            eprintln!(
                "Failed to parse manifest {}: {e}",
                global_manifest.display()
            );
            return 1;
        }
    };

    let mut total = 0usize;
    let mut passed = 0usize;
    let mut failed_cases: Vec<(String, String)> = Vec::new();
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

        // Print progress with immediate flush
        eprint!(
            "Testing {}/{total}: {name}... ",
            passed + failed_cases.len() + 1
        );
        let _ = std::io::stderr().flush();
        let test_start = Instant::now();

        let expected_compile_exit = entry
            .get("compileexitcode")
            .and_then(|v| v.as_i64())
            .map(|v| v as i32)
            .unwrap_or(0);

        let expected_runtime_exit = entry
            .get("exitcode")
            .and_then(|v| v.as_i64())
            .map(|v| v as i32)
            .unwrap_or(0);

        let source_rel = entry
            .get("source")
            .and_then(|v| v.as_array())
            .and_then(|arr| arr.first())
            .and_then(|v| v.as_str())
            .map(|s| s.to_string());

        let input_rel = entry
            .get("input")
            .and_then(|v| v.as_array())
            .and_then(|arr| arr.first())
            .and_then(|v| v.as_str())
            .map(|s| s.to_string());

        let output_rel = entry
            .get("output")
            .and_then(|v| v.as_array())
            .and_then(|arr| arr.first())
            .and_then(|v| v.as_str())
            .map(|s| s.to_string());

        let Some(source_rel) = source_rel else {
            failed_cases.push((name.clone(), "manifest missing source path".to_string()));
            continue;
        };

        // Read source file
        let source_path = path.join(&source_rel);
        let src = match fs::read_to_string(&source_path) {
            Ok(s) => s,
            Err(e) => {
                failed_cases.push((
                    name.clone(),
                    format!("failed to read source {}: {e}", source_path.display()),
                ));
                continue;
            }
        };

        // Compile to IR
        eprint!("compiling...");
        let _ = std::io::stderr().flush();
        let ir_text = match compile_source_to_ir(&src, &source_path) {
            Ok(ir) => ir,
            Err(e) => {
                if expected_compile_exit == 0 {
                    failed_cases.push((
                        name.clone(),
                        format!("compilation failed (expected success): {e}"),
                    ));
                    eprintln!("FAILED ({:.2}s)", test_start.elapsed().as_secs_f64());
                } else {
                    // Expected compilation failure
                    passed += 1;
                    passed_cases.push(name);
                    eprintln!("OK ({:.2}s)", test_start.elapsed().as_secs_f64());
                }
                continue;
            }
        };

        // If we expected compilation to fail but it succeeded
        if expected_compile_exit != 0 {
            failed_cases.push((
                name.clone(),
                format!("compilation succeeded but expected exit code {expected_compile_exit}"),
            ));
            eprintln!("FAILED ({:.2}s)", test_start.elapsed().as_secs_f64());
            continue;
        }

        // Read input file
        let stdin_data = if let Some(input_rel) = input_rel {
            let input_path = path.join(&input_rel);
            match fs::read(&input_path) {
                Ok(data) => data,
                Err(e) => {
                    failed_cases.push((
                        name.clone(),
                        format!("failed to read input {}: {e}", input_path.display()),
                    ));
                    continue;
                }
            }
        } else {
            Vec::new()
        };

        // Read expected output file
        let expected_output = if let Some(output_rel) = output_rel {
            let output_path = path.join(&output_rel);
            match fs::read_to_string(&output_path) {
                Ok(out) => out,
                Err(e) => {
                    failed_cases.push((
                        name.clone(),
                        format!(
                            "failed to read expected output {}: {e}",
                            output_path.display()
                        ),
                    ));
                    continue;
                }
            }
        } else {
            String::new()
        };

        // Run the compiled IR
        eprint!("running...");
        let _ = std::io::stderr().flush();
        let timeout = Duration::from_secs(10);
        let result = match compile_and_run_ir(&ir_text, &stdin_data, timeout) {
            Ok(res) => res,
            Err(e) => {
                failed_cases.push((name.clone(), format!("execution failed: {e}")));
                continue;
            }
        };

        // Check exit code
        if result.exit_code != expected_runtime_exit {
            failed_cases.push((
                name.clone(),
                format!(
                    "exit code mismatch: expected {expected_runtime_exit}, got {}",
                    result.exit_code
                ),
            ));
            continue;
        }

        // Compare output
        // Strategy: if expected output has very few whitespace chars relative to length,
        // compare by removing all whitespace from both. Otherwise compare by tokens.
        let expected_ws_count = expected_output
            .chars()
            .filter(|c| c.is_whitespace())
            .count();
        let expected_len = expected_output.len();

        let use_normalized_compare =
            expected_len > 0 && (expected_ws_count as f64 / expected_len as f64) < 0.1;

        let matches = if use_normalized_compare {
            // Remove all whitespace and compare
            let expected_normalized: String = expected_output
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect();
            let actual_normalized: String = result
                .stdout
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect();
            expected_normalized == actual_normalized
        } else {
            // Compare by tokens
            let expected_tokens: Vec<&str> = expected_output.split_whitespace().collect();
            let actual_tokens: Vec<&str> = result.stdout.split_whitespace().collect();
            expected_tokens == actual_tokens
        };

        if !matches {
            let diff = if use_normalized_compare {
                let expected_normalized: String = expected_output
                    .chars()
                    .filter(|c| !c.is_whitespace())
                    .collect();
                let actual_normalized: String = result
                    .stdout
                    .chars()
                    .filter(|c| !c.is_whitespace())
                    .collect();
                format!(
                    "output mismatch (normalized comparison):\n  Expected length: {} chars\n  Got length: {} chars\n  First 50 chars expected: {:?}\n  First 50 chars got: {:?}",
                    expected_normalized.len(),
                    actual_normalized.len(),
                    expected_normalized.chars().take(50).collect::<String>(),
                    actual_normalized.chars().take(50).collect::<String>()
                )
            } else {
                let expected_tokens: Vec<&str> = expected_output.split_whitespace().collect();
                let actual_tokens: Vec<&str> = result.stdout.split_whitespace().collect();

                if expected_tokens.len() != actual_tokens.len() {
                    format!(
                        "output token count mismatch: expected {} tokens, got {} tokens\n  First 10 tokens expected: {:?}\n  First 10 tokens got: {:?}",
                        expected_tokens.len(),
                        actual_tokens.len(),
                        expected_tokens.iter().take(10).collect::<Vec<_>>(),
                        actual_tokens.iter().take(10).collect::<Vec<_>>()
                    )
                } else {
                    // Find first differing token
                    let mut diff_pos = 0;
                    for (i, (exp, act)) in
                        expected_tokens.iter().zip(actual_tokens.iter()).enumerate()
                    {
                        if exp != act {
                            diff_pos = i;
                            break;
                        }
                    }
                    format!(
                        "output mismatch at token {}:\n  Expected: '{}'\n  Got:      '{}'\n  Context: {:?}",
                        diff_pos + 1,
                        expected_tokens.get(diff_pos).unwrap_or(&""),
                        actual_tokens.get(diff_pos).unwrap_or(&""),
                        expected_tokens
                            .iter()
                            .skip(diff_pos.saturating_sub(2))
                            .take(5)
                            .collect::<Vec<_>>()
                    )
                }
            };
            failed_cases.push((name.clone(), diff));
            eprintln!("FAILED ({:.2}s)", test_start.elapsed().as_secs_f64());
            continue;
        }

        // Test passed
        passed += 1;
        passed_cases.push(name);
        eprintln!("OK ({:.2}s)", test_start.elapsed().as_secs_f64());
    }

    println!("\nIR tests: {passed}/{total} passed");

    if !passed_cases.is_empty() {
        println!("Passed cases:");
        for name in &passed_cases {
            println!("  ✓ {name}");
        }
        println!();
    }

    if !failed_cases.is_empty() {
        println!("Failed cases:");
        for (name, msg) in &failed_cases {
            println!("  ✗ {name}:\n    {}", msg.replace('\n', "\n    "));
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

// Helper function to compile source code to IR
fn compile_source_to_ir(src: &str, source_path: &Path) -> Result<String, String> {
    let result = panic::catch_unwind(AssertUnwindSafe(|| -> Result<String, String> {
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
        let module_name = source_path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("module")
            .to_string();
        let lower = Lower::new(&nodes, &analyzer.type_context);
        let ir_module = lower
            .lower_program(&module_name)
            .map_err(|err| err.to_string())?;
        let ir_text = emit_module(&ir_module);

        // Validate with llvm-as
        validate_with_llvm_as(&ir_text)?;

        Ok(ir_text)
    }));

    match result {
        Ok(inner) => inner,
        Err(_) => {
            Err("panic during compilation (likely invalid UTF-8 boundary in lexer)".to_string())
        }
    }
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

    if flag == "--ir-test" {
        let maybe_dir = args.next().or_else(|| Some("testcases/IR-1".to_string()));
        let code = run_ir_tests(maybe_dir);
        let overall_duration = overall_start.elapsed();
        eprintln!(
            "Overall execution time: {:.3}ms",
            overall_duration.as_secs_f64() * 1000.0
        );
        if code != 0 { /* failure already reported */ }
        return;
    }

    if flag == "--playground" {
        let code = run_playground();
        let overall_duration = overall_start.elapsed();
        eprintln!(
            "Overall execution time: {:.3}ms",
            overall_duration.as_secs_f64() * 1000.0
        );
        if code != 0 { /* failure already reported */ }
        return;
    }

    if flag == "--emit-ir" {
        // Read source from stdin if no file provided, or from file if provided
        let input_path = args.next().map(PathBuf::from);
        let src = match read_source(input_path.as_deref().map(|p| p.to_str().unwrap())) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("failed to read input: {e}");
                return;
            }
        };
        let code = run_emit_ir(src, input_path.as_deref());
        if code != 0 { /* failure */ }
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

    while let Some(arg) = args.next() {
        if arg == "--out" {
            let Some(p) = args.next() else {
                eprintln!("--out requires a path");
                return;
            };
            out_path = Some(PathBuf::from(p));
        } else if arg.starts_with("--") {
            eprintln!("Unknown option: {arg}");
            print_usage();
            return;
        } else if input_path.is_none() {
            input_path = Some(PathBuf::from(arg));
        } else {
            eprintln!("Too many positional arguments");
            print_usage();
            return;
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

    let code = run_emit(
        pretty_flag,
        src,
        out_path.as_deref(),
        input_path.as_deref(),
        None,
        false,
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

fn run_emit_ir(src: String, input_path: Option<&Path>) -> i32 {
    // Lex
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

    // Parse
    let mut parser = Parser::new(tokens);
    let nodes = match parser.parse() {
        Ok(n) => n,
        Err(e) => {
            eprintln!("parse error: {e}");
            return 1;
        }
    };

    // Analyze
    let mut analyzer = Analyzer::new();
    if let Err(e) = analyzer.analyse_program(&nodes) {
        eprintln!("semantic error: {e}");
        return 1;
    }

    // Lower to IR
    let module_name = input_module_name(None, false, input_path);
    let lower = Lower::new(&nodes, &analyzer.type_context);
    let ir_module = match lower.lower_program(&module_name) {
        Ok(module) => module,
        Err(err) => {
            eprintln!("lowering error: {err}");
            return 1;
        }
    };
    let ir_text = emit_module(&ir_module);

    // Validate
    if let Err(err) = validate_with_llvm_as(&ir_text) {
        eprintln!("LLVM IR validation error: {err}");
        return 1;
    }

    // Output to stdout
    println!("{ir_text}");

    // Don't print timing when emitting IR, as it pollutes the IR output
    // The `run_emit_ir` function is implicitly for emitting IR, so we always skip timing here.
    // if !emit_ir { // `emit_ir` is not defined in this scope.
    //     eprintln!(\"Total time: {:.3}ms\", duration.as_secs_f64() * 1000.0);
    // }
    // The instruction was to "Comment out the timing output when emit_ir is true".
    // Since this function *is* the emit_ir path, we simply comment out the timing.
    // eprintln!("Total time: {:.3}ms", duration.as_secs_f64() * 1000.0);

    0
}
