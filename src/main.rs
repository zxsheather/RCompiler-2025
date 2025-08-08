mod frontend;
use frontend::r_lexer::lexer::Lexer;
use frontend::r_parser::parser::Parser;

use std::fs;
use std::path::{Path, PathBuf};

fn main() {
    // Default to processing the ./testcases directory; allow overriding via first CLI arg
    let target = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("testcases"));

    let mut total = 0usize;
    let mut passed = 0usize;
    let mut failed = 0usize;

    if target.is_dir() {
        let mut entries: Vec<_> = fs::read_dir(&target)
            .unwrap_or_else(|e| panic!("read_dir {} failed: {e}", target.display()))
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| p.extension().map(|ext| ext == "rx").unwrap_or(false))
            .collect();
        entries.sort();
        for path in entries {
            let (t, p, f) = process_file(&path);
            total += t;
            passed += p;
            failed += f;
        }
    } else if target.is_file() {
        let (t, p, f) = process_file(&target);
        total += t;
        passed += p;
        failed += f;
    } else {
        eprintln!("Path not found: {}", target.display());
        std::process::exit(1);
    }

    println!("\nSummary: total={}, passed={}, failed={}", total, passed, failed);
    if failed > 0 { std::process::exit(1); }
}

fn process_file(path: &Path) -> (usize, usize, usize) {
    println!("==> {}", path.display());
    let src = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("  Read error: {e}");
            return (1, 0, 1);
        }
    };

    let expect_error = detect_expect_error_marker(&src);

    // Lexing
    let mut lexer = match Lexer::new(src.clone()) {
        Ok(l) => l,
        Err(e) => {
            if expect_error {
                println!("  ✓ Expected lex error: {:?}", e);
                return (1, 1, 0);
            } else {
                eprintln!("  ✗ Lexer init error: {:?}", e);
                return (1, 0, 1);
            }
        }
    };

    let tokens = match lexer.tokenize() {
        Ok(toks) => toks,
        Err(e) => {
            if expect_error {
                println!("  ✓ Expected lex error: {:?}", e);
                return (1, 1, 0);
            } else {
                eprintln!("  ✗ Lex error: {:?}", e);
                return (1, 0, 1);
            }
        }
    };

    // Parsing
    let mut parser = Parser::new(tokens);
    match parser.parse() {
        Ok(ast) => {
            if expect_error {
                eprintln!("  ✗ Expected error, but parsed OK. AST nodes: {}", ast.len());
                (1, 0, 1)
            } else {
                println!("  ✓ Parse OK ({} nodes)", ast.len());
                (1, 1, 0)
            }
        }
        Err(e) => {
            if expect_error {
                println!("  ✓ Expected parse error: {:?}", e);
                (1, 1, 0)
            } else {
                eprintln!("  ✗ Parse error: {:?}", e);
                (1, 0, 1)
            }
        }
    }
}

// Heuristic: treat "// -1" or a comment containing "error" in the first non-empty comment line as expecting an error
fn detect_expect_error_marker(src: &str) -> bool {
    for line in src.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() { continue; }
        if let Some(rest) = trimmed.strip_prefix("//") {
            let marker = rest.trim().to_lowercase();
            if marker.contains("-1") || marker.contains("error") { return true; }
            // If first non-empty is a comment but doesn't indicate error, continue scanning a bit
            continue;
        }
        // First non-empty, non-comment line reached
        break;
    }
    false
}
