mod frontend;

use std::env;
use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::time::Instant;

use frontend::r_lexer::lexer::Lexer;
use frontend::r_parser::parser::Parser;
use std::panic::{self, AssertUnwindSafe};

use crate::frontend::r_semantic::analyzer::Analyzer;

fn print_usage() {
    eprintln!(
        "Usage:
  RCompiler-2025 --ast-json  [INPUT] [--out OUTPUT]
  RCompiler-2025 --ast-pretty [INPUT] [--out OUTPUT]
  RCompiler-2025 --semantic-test [TESTDIR]
  RCompiler-2025 --semantic-test-2 [TESTDIR]

Notes:
  - If INPUT is omitted, source is read from stdin.
  - One of --ast-json or --ast-pretty must be provided.
  - If --out is omitted, result is printed to stdout.
  - --semantic-test will run all semantic tests under testcases/semantic-1 by default.
  - --semantic-test-2 will run all semantic tests under testcases/semantic-2 by default."
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

fn run_emit(pretty_out: bool, src: String, out_path: Option<&Path>) -> i32 {
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
        "  Total:      {:>8.3}ms",
        total_duration.as_secs_f64() * 1000.0
    );

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

fn run_semantic_tests(root: Option<String>) -> i32 {
    let start_time = Instant::now();

    let test_root = root.unwrap_or_else(|| "testcases/semantic-1".to_string());
    let path = Path::new(&test_root);
    if !path.exists() {
        eprintln!("Test root not found: {}", path.display());
        return 1;
    }

    // Helper to run one case directory
    fn run_case(case_dir: &Path) -> Option<(String, i32, i32, String)> {
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
        let rx_path = rx_file?;
        let expected = expected_exit.unwrap_or(0);
        let src = match fs::read_to_string(&rx_path) {
            Ok(s) => s,
            Err(_) => {
                return Some((
                    case_dir.file_name().unwrap().to_string_lossy().to_string(),
                    expected,
                    -999,
                    "read source failed".to_string(),
                ));
            }
        };
        let res = compile_semantic(&src);
        let actual_std = if res.is_ok() { 0 } else { -1 };
        if actual_std == expected {
            None
        } else {
            Some((
                case_dir.file_name().unwrap().to_string_lossy().to_string(),
                expected,
                actual_std,
                res.err().unwrap_or_else(|| "<unknown error>".to_string()),
            ))
        }
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

    if is_single_case {
        total = 1;
        if let Some(fail) = run_case(path) {
            failed_cases.push(fail);
        } else {
            passed = 1;
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
            total += 1; // count first; adjust inside run_case
            if let Some(fail) = run_case(&entry.path()) {
                failed_cases.push(fail);
            } else {
                passed += 1;
            }
        }
    }

    println!("Semantic tests: {passed}/{total} passed");
    if !failed_cases.is_empty() {
        println!("Failed cases:");
        for (name, exp, act, msg) in &failed_cases {
            println!("  {name}: expected {exp}, got {act}\n    error: {msg}");
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

    let code = run_emit(pretty_flag, src, out_path.as_deref());
    let overall_duration = overall_start.elapsed();
    eprintln!(
        "Overall execution time: {:.3}ms",
        overall_duration.as_secs_f64() * 1000.0
    );
    if code != 0 {
        // non-zero exit code path (no process::exit to preserve Drops)
    }
}
