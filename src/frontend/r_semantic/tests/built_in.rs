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

// === Positive cases ===

#[test]
fn builtin_print_with_literal_ok() {
    let src = r#"fn main() { print("hi"); println("ok"); }"#;
    match analyze_src(src) {
        Ok(_) => {}
        Err(e) => panic!("unexpected error: {e}"),
    }
}

#[test]
fn builtin_print_with_str_slice_ok() {
    let src = r#"fn main() { let s: &str = "world"; println(s); }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn builtin_print_with_string_via_as_str_ok() {
    let src = r#"fn main() { let mut s: String = getString(); print(s.as_str()); }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn builtin_println_int_ok() {
    let src = r#"fn main() { let n: i32 = 3; printlnInt(n); printInt(1 + 2); }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn get_string_assign_ok() {
    let src = r#"fn main() { let s: String = getString(); }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn get_int_use_ok() {
    let src = r#"fn main() { let a: i32 = readInt(); let b: i32 = readInt(); printlnInt(a + b); }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn to_string_on_u32_ok() {
    let src = r#"fn main() { let x: u32 = 10u32; let s: String = x.to_string(); }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn len_methods_ok() {
    let src = r#"fn main() { let mut s: String = getString(); let p: &str = s.as_str(); let m: &mut str = s.as_mut_str(); let l1: usize = s.len(); let l2: usize = p.len(); let l3: usize = m.len(); let a: [i32;3] = [1,2,3]; let l4: usize = a.len(); }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn string_from_and_append_ok() {
    let src = r#"fn main() { let mut s: String = getString(); let p: &str = s.as_str(); s.append(p); let t: String = String::from(p); let pm: &mut str = s.as_mut_str(); let t2: String = String::from(pm); }"#;
    assert!(analyze_src(src).is_ok());
}

// === Negative cases ===

#[test]
fn print_with_string_without_as_str_error() {
    let src = r#"fn main() { let s: String = getString(); print(s); }"#; // expects &str
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected '&str'"), "err: {err}");
}

#[test]
fn println_int_with_bool_error() {
    let src = r#"fn main() { printlnInt(true); }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected 'i32'"), "err: {err}");
}

#[test]
fn get_string_assign_to_str_slice_error() {
    let src = r#"fn main() { let p: &str = getString(); }"#; // returns String
    let err = analyze_src(src).unwrap_err();
    assert!(
        err.contains("expected &str") || err.contains("expected &str"),
        "err: {err}"
    );
}

#[test]
fn append_on_immutable_string_error() {
    let src =
        r#"fn main() { let s: String = getString(); let p: &str = s.as_str(); s.append(p); }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected '&mut String'"), "err: {err}");
}

#[test]
fn len_on_type_without_method_error() {
    let src = r#"fn main() { let x: i32 = 1; let l: usize = x.len(); }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("found i32"), "err: {err}");
}

#[test]
fn string_from_wrong_arg_type_error() {
    let src = r#"fn main() { let x: i32 = 1; let s: String = String::from(x); }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected '&str'"), "err: {err}");
}
