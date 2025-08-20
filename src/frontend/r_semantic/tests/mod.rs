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
    // println!("Error: {err}");
    assert!(err.contains("expected 'i32' but got 'bool'"), "err: {err}");
}

#[test]
fn if_branch_type_mismatch() {
    let src = r#"fn f(a: bool) -> i32 { if a { 1 } else { true } }"#;
    let err = analyze_src(src).unwrap_err();
    // println!("Error: {err}");
    assert!(err.contains("Mismatched branch types"), "err: {err}");
}

#[test]
fn function_return_type_mismatch() {
    let src = r#"fn f() -> i32 { true }"#;
    let err = analyze_src(src).unwrap_err();
    // println!("Error: {err}");
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

#[test]
fn struct_methods_ok() {
    let src = r#"
        struct Point { x: i32, y: i32 }
        impl Point {
            fn sum(self: Point) -> i32 { self.x + self.y }
            fn add_x(self: Point, v: i32) -> i32 { self.x + v }
        }
        fn main() { let p: Point = Point { x: 1, y: 2 }; let s: i32 = p.sum(); let t: i32 = p.add_x(3); }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn struct_method_wrong_args() {
    let src = r#"
        struct Point { x: i32, y: i32 }
        impl Point { fn add_x(self: Point, v: i32) -> i32 { self.x + v } }
        fn main() { let p: Point = Point { x: 1, y: 2 }; let s = p.add_x(true); }
    "#;
    let err = analyze_src(src).unwrap_err();
    // println!("{:?}", err);
    assert!(err.contains("expected 'i32'"), "err: {err}");
}

#[test]
fn static_methods_ok() {
    let src = r#"
        struct Point { x: i32, y: i32 }
        impl Point { fn make(x: i32, y: i32) -> Point { Point { x: x, y: y } } }
        fn main() { let p: Point = Point::make(1, 2); }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn static_method_wrong_args() {
    let src = r#"
        struct Point { x: i32, y: i32 }
        impl Point { fn make(x: i32, y: i32) -> Point { Point { x: x, y: y } } }
        fn main() { let p: Point = Point::make(true, 2); }
    "#;
    let err = analyze_src(src).unwrap_err();
    // println!("{:?}", err);
    assert!(err.contains("expected 'i32'"), "err: {err}");
}

#[test]
fn struct_literal_shorthand_semantic() {
    let src = r#"
        struct Point { x: i32, y: i32 }
        fn id(x: i32) -> i32 { x }
        fn main() { let x: i32 = 1; let y: i32 = 2; let p: Point = Point { x, y }; let a: i32 = id(p.x); }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn array_element_assignment_ok() {
    let src = r#"
        fn main() { let mut a: [i32; 3] = [1, 2, 3]; a[1] = 42; }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn array_element_assignment_type_error() {
    let src = r#"
        fn main() { let mut a: [i32; 3] = [1, 2, 3]; a[1] = true; }
    "#;
    let err = analyze_src(src).unwrap_err();
    // println!("{:?}", err);
    assert!(err.contains("Type mismatch in assignment"), "err: {err}");
}

#[test]
fn array_element_assignment_immutable_error() {
    let src = r#"
        fn main() { let a: [i32; 2] = [1, 2]; a[0] = 3; }
    "#;
    let err = analyze_src(src).unwrap_err();
    // println!("{:?}", err);
    assert!(err.contains("immutable"), "err: {err}");
}

#[test]
fn struct_field_assignment_ok() {
    let src = r#"
        struct Point { x: i32, y: i32 }
        fn main() { let mut p: Point = Point { x: 1, y: 2 }; p.x = 3; }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn struct_field_assignment_type_error() {
    let src = r#"
        struct Point { x: i32, y: i32 }
        fn main() { let mut p: Point = Point { x: 1, y: 2 }; p.x = true; }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("Type mismatch in assignment"), "err: {err}");
}

#[test]
fn struct_field_assignment_immutable_error() {
    let src = r#"
        struct Point { x: i32, y: i32 }
        fn main() { let p: Point = Point { x: 1, y: 2 }; p.x = 3; }
    "#;
    let err = analyze_src(src).unwrap_err();
    // println!("{:?}", err);
    assert!(err.contains("immutable"), "err: {err}");
}

#[test]
fn trait_decl_and_impl_ok_and_dispatch() {
    let src = r#"
        struct Point { x: i32, y: i32 }
        trait Sum {
            fn sum(self: Point) -> i32;
        }
        impl Sum for Point {
            fn sum(self: Point) -> i32 { self.x + self.y }
        }
        fn main() {
            let p: Point = Point { x: 1, y: 2 };
            let s: i32 = p.sum();
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn trait_impl_missing_method_error() {
    let src = r#"
        struct S { a: i32 }
        trait T { fn sum(self: S) -> i32; }
        impl T for S { }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("missing method"), "err: {err}");
}

#[test]
fn trait_impl_signature_mismatch_error() {
    let src = r#"
        struct S { a: i32 }
        trait T { fn sum(self: S, b: i32) -> i32; }
        impl T for S { fn sum(self: S, b: bool) -> i32 { 0 } }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("Signature mismatch"), "err: {err}");
}

#[test]
fn references_basic_and_types() {
    let src = r#"
        struct Point { x: i32, y: i32 }
        fn takes_ref_i32(a: &i32) { }
        fn takes_ref_mut_point(p: &mut Point) { }
        fn main() {
            let x: i32 = 1;
            let mut p: Point = Point { x: 1, y: 2 };
            let r1 = &x; // &i32
            let r2 = &mut p; // &mut Point
            takes_ref_i32(r1);
            takes_ref_mut_point(r2);
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn references_auto_deref_member_and_index() {
    let src = r#"
        struct Point { x: i32, y: i32 }
        fn main() {
            let p: Point = Point { x: 1, y: 2 };
            let rp = &p;
            let a: [i32; 3] = [1, 2, 3];
            let ra = &a;
            let v1: i32 = rp.x; // auto-deref for member
            let v2: i32 = ra[0]; // auto-deref for index
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn method_call_on_borrowed_receiver() {
    let src = r#"
        struct Point { x: i32, y: i32 }
        impl Point {
            fn sum(self: &Point) -> i32 { self.x + self.y }
            fn bump_x(self: &mut Point, v: i32) -> i32 { self.x + v }
        }
        fn main() {
            let p: Point = Point { x: 1, y: 2 };
            let rp = &p;
            let s: i32 = rp.sum();
            let mut q: Point = Point { x: 3, y: 4 };
            let rqm = &mut q;
            let t: i32 = rqm.bump_x(5);
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn borrow_mut_from_immutable_error() {
    let src = r#"
        fn main() {
            let x: i32 = 1;
            let rx = &mut x;
        }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(
        err.contains("Cannot take mutable reference to immutable value"),
        "err: {err}"
    );
}

#[test]
fn assign_through_mut_array_ref_ok() {
    let src = r#"
        fn main() {
            let mut a: [i32; 3] = [1,2,3];
            let ra: &mut [i32; 3] = &mut a;
            ra[1] = 42;
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn assign_through_immutable_array_ref_error() {
    let src = r#"
        fn main() {
            let a: [i32; 3] = [1,2,3];
            let ra: &[i32; 3] = &a;
            ra[1] = 42;
        }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("immutable"), "err: {err}");
}

#[test]
fn assign_through_mut_struct_ref_ok() {
    let src = r#"
        struct P { x: i32 }
        fn main() {
            let mut p: P = P { x: 1 };
            let rp: &mut P = &mut p;
            rp.x = 2;
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn method_requires_mut_receiver_error() {
    let src = r#"
        struct P { x: i32 }
        impl P {
            fn set_x(self: &mut P, v: i32) -> i32 { self.x + v }
        }
        fn main() {
            let p: P = P { x: 1 };
            let rp = &p;
            rp.set_x(2);
        }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected '&mut P'"), "err: {err}");
}
