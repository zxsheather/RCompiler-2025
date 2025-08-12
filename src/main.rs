mod frontend;

use std::env;
use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};

use frontend::r_lexer::lexer::Lexer;
use frontend::r_parser::parser::Parser;

use crate::frontend::r_semantic::analyzer::Analyzer;

fn print_usage() {
    eprintln!(
        "Usage:
  RCompiler-2025 --ast-json  [INPUT] [--out OUTPUT]
  RCompiler-2025 --ast-pretty [INPUT] [--out OUTPUT]

Notes:
  - If INPUT is omitted, source is read from stdin.
  - One of --ast-json or --ast-pretty must be provided.
  - If --out is omitted, result is printed to stdout."
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

    // Emit
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

    // Analyzing
    let mut analyzer = Analyzer::new();
    if let Err(e) = analyzer.analyse_program(&nodes) {
        eprintln!("semantic error: {e}");
        return 1;
    }

    0
}

fn main() {
    let mut args = env::args().skip(1);
    let Some(flag) = args.next() else {
        print_usage();
        return;
    };

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
    if code != 0 {
        // non-zero exit code path (no process::exit to preserve Drops)
    }
}
