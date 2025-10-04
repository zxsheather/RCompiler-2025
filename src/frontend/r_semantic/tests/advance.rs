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
fn select_k() {
    let src = r#"
    fn partition(a: &mut [i32; 11], low: usize, high: usize) -> usize {
        let pivot: i32 = a[high];
        let mut i: usize = low;
        let mut j: usize = low;
        while (j < high) {
            if (a[j] < pivot) {
                let tmp: i32 = a[i];
                a[i] = a[j];
                a[j] = tmp;
                i += 1;
            }
            j += 1;
        }
        let tmp: i32 = a[i];
        a[i] = a[high];
        a[high] = tmp;
        i
    }
    fn select_k(a: &mut [i32; 11], low: usize, high: usize, k: usize) -> i32 {
        if (low == high) {
            return a[low];
        }
        let p: usize = partition(a, low, high);
        if (k == p) {
            a[p]
        } else if (k < p) {
            select_k(a, low, p - 1, k)
        } else {
            select_k(a, p + 1, high, k)
        }
    }
    fn main() {
        let mut values: [i32; 11] = [42, 7, 13, 99, 5, 8, 1, 77, 56, 23, 11];
        let median_index: usize = 5usize;
        let median: i32 = select_k(&mut values, 0, 10, median_index);
        exit(0);
    }"#;
    match analyze_src(src) {
        Ok(_) => {}
        Err(e) => panic!("unexpected error: {e}"),
    }
}

// #[test]
// fn fn_redeclare() {
//     let src = r#"
//     fn add(a: i32, b: i32) -> i32 {
//         a + b
//     }
//     fn add(a: i32, b: i32) -> i32 {
//         a - b
//     }
//     "#;
//     let err = analyze_src(src).unwrap_err();
//     assert!(err.contains("redeclared"), "err: {err}");
// }

#[test]
fn div() {
    let src = r#"
    const LEN: usize = 3;
    fn main() {
        let a: i32 = 10;
        let c: i32 = a / LEN;
    }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("type"), "err: {err}");
}
