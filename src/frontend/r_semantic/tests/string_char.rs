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
fn string_literal_type_assign_to_str_ref_ok() {
    let src = r#"fn main() { let s: &str = "hello"; }"#; // if &str supported directly
    // Currently type system: &str literal type is &str; accept
    assert!(analyze_src(src).is_ok());
}

#[test]
fn string_methods_ok() {
    let src = r#"
        fn main() {
            let mut s: String = getString();
            let p: &str = s.as_str();
            let pm: &mut str = s.as_mut_str();
            let l: usize = s.len();
            let lslice: usize = p.len();
            let lmut: usize = pm.len();
            s.append(p);
            let t: String = String::from(p);
            let n: u32 = 123u32;
            let sn: String = n.to_string(); // test primitive method on u32
        }
    "#;
    match analyze_src(src) {
        Ok(_) => {}
        Err(e) => panic!("unexpected error: {e}"),
    }
}

#[test]
fn append_requires_mut_self_error() {
    let src = r#"
        fn main() {
            let s: String = getString();
            let p: &str = s.as_str();
            s.append(p); // immutable self
        }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected '&mut String'"), "err: {err}");
}

#[test]
fn from_requires_str_arg_type_error() {
    let src = r#"
        fn main() {
            let mut s: String = getString();
            let x: i32 = 1;
            let t: String = String::from(x); // wrong arg
        }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected '&str'"), "err: {err}");
}

#[test]
fn char_literal_type_ok() {
    let src = r#"fn main() { let c: char = 'a'; }"#;
    assert!(analyze_src(src).is_ok());
}
