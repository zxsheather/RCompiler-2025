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

#[test]
fn cast_int_literal_to_i32_ok() {
    let src = "fn main(){ let x: i32 = 123 as i32; }";
    assert!(analyze_src(src).is_ok());
}

#[test]
fn cast_int_literal_to_u32_ok() {
    let src = "fn main(){ let x: u32 = 123 as u32; }";
    assert!(analyze_src(src).is_ok());
}

#[test]
fn cast_between_concrete_ints_ok() {
    let src = "fn main(){ let a: i32 = 1; let b: i32 = (a as i32); }"; // same type still allowed
    assert!(analyze_src(src).is_ok());
}

#[test]
fn cast_int_to_different_int_ok() {
    let src = "fn main(){ let a: i32 = 1; let b: u32 = a as u32; }";
    assert!(analyze_src(src).is_ok());
}

#[test]
fn cast_bool_to_int_ok() {
    let src = "fn main(){ let b: bool = true; let x: i32 = b as i32; }";
    match analyze_src(src) {
        Ok(()) => {}
        Err(err) => panic!("Unexpected error: {err}"),
    }
}

#[test]
fn cast_int_to_bool_target_not_int_error() {
    let src = "fn main(){ let a: i32 = 1; let b: bool = a as bool; }"; // target bool not allowed by rule
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("Only integer can be casted to"), "err: {err}");
}

#[test]
fn cast_char_to_i32_ok() {
    let src = "fn main(){ let c: char = 'a'; let x: i32 = c as i32; }";
    assert!(analyze_src(src).is_ok());
}

#[test]
fn cast_string_to_i32_err() {
    let src = "fn main(){ let s: String = String::from(\"hello\"); let x: i32 = s as i32; }";
    let err = analyze_src(src).unwrap_err();
    assert!(
        err.contains("Only integer, char, bool can be casted"),
        "err: {err}"
    );
}
