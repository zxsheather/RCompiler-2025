use crate::frontend::r_lexer::lexer::Lexer;
use crate::frontend::r_parser::parser::Parser;
use crate::frontend::r_semantic::analyzer::Analyzer;

fn analyze_src(src: &str) -> Result<(), String> {
    let mut lexer = Lexer::new(src.to_string()).map_err(|e| format!("lex init: {e}"))?;
    let tokens = lexer.tokenize().map_err(|e| format!("lex: {e}"))?;
    let mut parser = Parser::new(tokens);
    let nodes = parser.parse().map_err(|e| format!("parse: {e}"))?;
    let mut analyzer = Analyzer::new();
    analyzer.analyse_program(&nodes).map_err(|e| e.to_string())
}

// === 正确用例 ===
#[test]
fn const_basic_ok() {
    let src = r#"fn main() { const x: i32 = 1; const z: bool = true; }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn const_use_in_array_ok() {
    let src = r#"fn main() { const x: usize = 1; let mut arr: [i32; 3] = [0, 0, 0]; arr[x] = 1; const idx: usize = 2; arr[idx] = arr[idx] + x; }"#;
    match analyze_src(src) {
        Ok(_) => {}
        Err(e) => panic!("unexpected error: {e}"),
    }
}

#[test]
fn const_expr_ok() {
    let src = r#"fn main() { const a: i32 = 2; const b: i32 = a + 3; const c: usize = 5; let mut arr: [i32; b] = [0; b]; arr[c - 2] = 10; }"#;
    match analyze_src(src) {
        Ok(_) => {}
        Err(e) => panic!("unexpected error: {e}"),
    }
}

// === 错误用例 ===
#[test]
fn const_redeclare_error() {
    let src = r#"fn main() { const x: i32 = 1; const x: i32 = 2; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("already declared"), "err: {err}");
}

#[test]
fn const_uninitialized_error() {
    let src = r#"fn main() { const y: i32; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("Expected Eq"), "err: {err}");
}

#[test]
fn const_assign_error() {
    let src = r#"fn main() { const x: i32 = 1; x = 2; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("Undefined"), "err: {err}");
}

#[test]
fn const_type_mismatch_error() {
    let src = r#"fn main() { const x: i32 = "hello"; const y: bool = 123; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("type"), "err: {err}");
}
