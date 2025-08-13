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
fn analyzer_ok_simple() {
    let src = r#"
        fn add(a: i32, b: i32) -> i32 { a + b }
        fn main() { let mut x: i32 = 1; x = add(2, 3); }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn immutable_assignment_error() {
    let src = r#"fn main() { let x: i32 = 1; x = 2; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("immutable"), "err: {err}");
}

#[test]
fn undeclared_variable_error() {
    let src = r#"fn main() { y = 1; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("Undefined identifier"), "err: {err}");
}

#[test]
fn call_wrong_arg_type() {
    let src = r#"
        fn add(a: i32, b: i32) -> i32 { a + b }
        fn main() { let mut x: i32 = 0; x = add(1, true); }
    "#;
    let err = analyze_src(src).unwrap_err();
    println!("Error: {err}");
    assert!(err.contains("expected 'i32' but got 'bool'"), "err: {err}");
}

#[test]
fn if_branch_type_mismatch() {
    let src = r#"fn f(a: bool) -> i32 { if a { 1 } else { true } }"#;
    let err = analyze_src(src).unwrap_err();
    println!("Error: {err}");
    assert!(err.contains("Mismatched branch types"), "err: {err}");
}

#[test]
fn function_return_type_mismatch() {
    let src = r#"fn f() -> i32 { true }"#;
    let err = analyze_src(src).unwrap_err();
    println!("Error: {err}");
    assert!(err.contains("expected i32, found bool"), "err: {err}");
}

#[test]
fn array_index_ok() {
    let src = r#"fn f(a: [i32; 3]) { let x: i32 = a[0]; }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn array_index_type_error() {
    let src = r#"fn f(a: [i32; 3]) { let x: i32 = a[true]; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("Invalid index type"), "err: {err}");
}

#[test]
fn mixed_array_literal_error() {
    let src = r#"fn main() { let a = [1, true]; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("Mixed typed array"), "err: {err}");
}

#[test]
fn tuple_types_flow() {
    let src = r#"
        fn make() -> (i32, bool) { (1, true) }
        fn main() {
            let t: (i32, bool) = make();
        }
    "#;
    // let err = analyze_src(src).unwrap_err();
    // println!("{}", err);
    assert!(analyze_src(src).is_ok());
}

#[test]
fn unit_tuple_is_unit() {
    let src = r#"fn main() { let x = (); }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn struct_type_flow_ok() {
    let src = r#"
        struct Point { x: i32, y: i32 }
    fn id(p: Point) -> Point { p }
    fn main() { let p: Point = id(Point { x: 1, y: 2 }); let v = p.x; }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn struct_field_type_mismatch() {
    let src = r#"
        struct S { a: i32 }
        fn main() { let s: S = S { a: true }; }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("type mismatch"), "err: {err}");
}
