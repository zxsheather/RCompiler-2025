use crate::frontend::r_lexer::lexer::Lexer;
use crate::frontend::r_parser::parser::Parser;
use crate::frontend::r_semantic::analyzer::Analyzer;
pub mod advance;
pub mod as_cast;
pub mod built_in;
pub mod consts;
pub mod string_char;

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
    match analyze_src(src) {
        Ok(()) => {}
        Err(err) => panic!("Unexpected error: {err}"),
    }
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
    match analyze_src(src) {
        Ok(()) => {}
        Err(err) => panic!("Unexpected error: {err}"),
    }
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
    match analyze_src(src) {
        Ok(()) => {}
        Err(err) => {
            panic!("Unexpected error: {err}");
        }
    }
}

#[test]
fn array_element_assignment_type_error() {
    let src = r#"
        fn main() { let mut a: [i32; 3] = [1, 2, 3]; a[1] = true; }
    "#;
    let err = analyze_src(src).unwrap_err();
    // println!("{:?}", err);
    assert!(err.contains("type mismatch"), "err: {err}");
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
    assert!(err.contains("type mismatched"), "err: {err}");
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
    match analyze_src(src) {
        Ok(()) => {}
        Err(err) => {
            panic!("Unexpected error: {err}");
        }
    }
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

#[test]
fn method_self_ref_sugar_borrow_ok() {
    let src = r#"
        struct P { x: i32 }
        impl P { fn get(&self) -> i32 { self.x } }
        fn main() { let p: P = P { x: 1 }; let v: i32 = p.get(); }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn method_self_ref_sugar_mut_borrow_ok() {
    let src = r#"
        struct P { x: i32 }
        impl P { fn set(&mut self, v: i32) -> i32 { self.x + v } }
        fn main() { let mut p: P = P { x: 1 }; let v: i32 = p.set(2); }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn method_self_ref_sugar_mut_on_immutable_error() {
    let src = r#"
        struct P { x: i32 }
        impl P { fn set(&mut self, v: i32) -> i32 { self.x + v } }
        fn main() { let p: P = P { x: 1 }; p.set(2); }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected '&mut P'"), "err: {err}");
}

#[test]
fn mutable_param_assignment_ok() {
    let src = r#"
        fn f(mut a: i32, b: i32) { a = a + 1; }
        fn main() { f(1, 2); }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn immutable_param_assignment_error() {
    let src = r#"
        fn f(a: i32) { a = 2; }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("immutable"), "err: {err}");
}

#[test]
fn method_auto_borrow_for_ref_receiver_ok() {
    let src = r#"
        struct P { x: i32 }
        impl P { fn get(self: &P) -> i32 { self.x } }
        fn main() {
            let p: P = P { x: 1 };
            // owned value calling &self method: auto &
            let v: i32 = p.get();
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn method_auto_borrow_mut_ok() {
    let src = r#"
        struct P { x: i32 }
        impl P { fn set(self: &mut P, v: i32) -> i32 { self.x + v } }
        fn main() {
            let mut p: P = P { x: 1 };
            // auto &mut because method expects &mut P and we have mutable owned p
            let r: i32 = p.set(2);
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn method_auto_borrow_mut_on_immutable_error() {
    let src = r#"
        struct P { x: i32 }
        impl P { fn set(self: &mut P, v: i32) -> i32 { self.x + v } }
        fn main() {
            let p: P = P { x: 1 }; // immutable
            p.set(2); // should fail: cannot auto &mut
        }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected '&mut P'"), "err: {err}");
}

#[test]
fn method_auto_deref_ref_to_owned_ok() {
    let src = r#"
        struct P { x: i32 }
        impl P { fn take(self: P) -> i32 { self.x } }
        fn main() {
            let p: P = P { x: 1 };
            let rp = &p;
            // calling owned self method on &P (auto-deref)
            let v: i32 = rp.take();
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn method_auto_deref_mut_ref_to_owned_ok() {
    let src = r#"
        struct P { x: i32 }
        impl P { fn take(self: P) -> i32 { self.x } }
        fn main() {
            let mut p: P = P { x: 1 };
            let rp = &mut p;
            let v: i32 = rp.take();
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

// === Additional robustness tests for self semantics (struct & trait) ===

#[test]
fn trait_impl_owned_self_call_ok() {
    let src = r#"
        struct S { v: i32 }
        trait Inc { fn inc(self: S, d: i32) -> i32; }
        impl Inc for S { fn inc(self: S, d: i32) -> i32 { self.v + d } }
        fn main() { let s: S = S { v: 1 }; let x: i32 = s.inc(2); }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn trait_impl_borrowed_self_call_auto_ref_ok() {
    let src = r#"
        struct S { v: i32 }
    trait Inc { fn inc(&self, d: i32) -> i32; }
        impl Inc for S { fn inc(self: &S, d: i32) -> i32 { self.v + d } }
        fn main() { let s: S = S { v: 1 }; // owned -> &S auto
            let x: i32 = s.inc(2); }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn trait_impl_borrowed_mut_self_call_auto_ref_mut_ok() {
    let src = r#"
        struct S { v: i32 }
    trait Inc { fn inc(&mut self, d: i32) -> i32; }
        impl Inc for S { fn inc(self: &mut S, d: i32) -> i32 { self.v = self.v + d; self.v } }
        fn main() { let mut s: S = S { v: 1 }; let x: i32 = s.inc(2); }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn trait_impl_borrowed_mut_self_call_auto_ref_mut_on_immutable_error() {
    let src = r#"
        struct S { v: i32 }
    trait Inc { fn inc(&mut self, d: i32) -> i32; }
        impl Inc for S { fn inc(self: &mut S, d: i32) -> i32 { self.v + d } }
        fn main() { let s: S = S { v: 1 }; s.inc(2); }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected '&mut S'"), "err: {err}");
}

#[test]
fn method_receiver_array_index_auto_borrow_mut_ok() {
    let src = r#"
        struct P { x: i32 }
        impl P { fn set(self: &mut P, v: i32) -> i32 { self.x = v; self.x } }
        fn main() {
            let mut arr: [P; 1] = [P { x: 1 }];
            let r: i32 = arr[0].set(5);
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn method_receiver_array_index_auto_borrow_mut_immutable_error() {
    let src = r#"
        struct P { x: i32 }
        impl P { fn set(self: &mut P, v: i32) -> i32 { self.x = v; self.x } }
        fn main() {
            let arr: [P; 1] = [P { x: 1 }];
            arr[0].set(5); // immutable root
        }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected '&mut P'"), "err: {err}");
}

#[test]
fn method_receiver_member_chain_auto_borrow_mut_ok() {
    let src = r#"
        struct Inner { x: i32 }
        struct Wrap { i: Inner }
        impl Inner { fn set(self: &mut Inner, v: i32) -> i32 { self.x = v; self.x } }
        fn main() {
            let mut w: Wrap = Wrap { i: Inner { x: 1 } };
            let r: i32 = w.i.set(10);
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn method_receiver_member_chain_auto_borrow_mut_immutable_error() {
    let src = r#"
        struct Inner { x: i32 }
        struct Wrap { i: Inner }
        impl Inner { fn set(self: &mut Inner, v: i32) -> i32 { self.x = v; self.x } }
        fn main() {
            let w: Wrap = Wrap { i: Inner { x: 1 } }; // immutable
            w.i.set(10);
        }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected '&mut Inner'"), "err: {err}");
}

#[test]
fn trait_with_ref_self_ok() {
    let src = r#"
        struct S { v: i32 }
        trait Show { fn show(&self) -> i32; }
        impl Show for S { fn show(&self) -> i32 { self.v } }
        fn main() { let s: S = S { v: 3 }; let x: i32 = s.show(); }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn trait_with_mut_ref_self_ok() {
    let src = r#"
        struct S { v: i32 }
        trait Incr { fn add(&mut self, d: i32) -> i32; }
        impl Incr for S { fn add(&mut self, d: i32) -> i32 { self.v = self.v + d; self.v } }
        fn main() { let mut s: S = S { v: 1 }; let r: i32 = s.add(4); }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn trait_with_mut_ref_self_on_immutable_var_error() {
    let src = r#"
        struct S { v: i32 }
        trait Incr { fn add(&mut self, d: i32) -> i32; }
        impl Incr for S { fn add(&mut self, d: i32) -> i32 { self.v + d } }
        fn main() { let s: S = S { v: 1 }; s.add(2); }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected '&mut S'"), "err: {err}");
}

#[test]
fn trait_self_kind_mismatch_error() {
    let src = r#"
        struct S { v: i32 }
        trait T { fn f(&self) -> i32; }
        impl T for S { fn f(self: S) -> i32 { self.v } }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("self kind mismatch"), "err: {err}");
}

#[test]
fn array_repeat_syntax_ok() {
    let src = r#"
        fn main() { let mut flags: [bool; 5] = [false; 5]; }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn array_repeat_size_parse_error() {
    let src = r#"
        fn main() { let flags = [0; true]; }
    "#; // size not integer literal -> parse error
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("Cannot convert"), "err: {err}");
}

#[test]
fn array_repeat_type_mismatch_inside_assignment() {
    let src = r#"
        fn main() { let a: [i32; 3] = [1; 2]; }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("Type mismatch in assignment"), "err: {err}");
}

// ===== Compound assignment operators tests =====

#[test]
fn compound_assign_var_ok() {
    let src = r#"
        fn main() { let mut x: i32 = 1; x += 2; x -= 1; x *= 3; x /= 2; x %= 2; x &= 1; x |= 2; x ^= 3; }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn compound_assign_var_immutable_error() {
    let src = r#"fn main() { let x: i32 = 1; x += 2; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("immutable"), "err: {err}");
}

#[test]
fn compound_assign_var_type_mismatch_error() {
    let src = r#"fn main() { let mut x: i32 = 1; x += true; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("type mismatch"), "err: {err}");
}

#[test]
fn compound_assign_array_elem_ok() {
    let src = r#"fn main() { let mut a: [i32; 2] = [1,2]; a[0] += 3; }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn compound_assign_array_elem_immutable_error() {
    let src = r#"fn main() { let a: [i32; 2] = [1,2]; a[0] += 3; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("immutable"), "err: {err}");
}

#[test]
fn compound_assign_struct_field_ok() {
    let src = r#"
        struct P { x: i32 }
        fn main() { let mut p: P = P { x: 1 }; p.x += 2; }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn compound_assign_struct_field_immutable_error() {
    let src = r#"
        struct P { x: i32 }
        fn main() { let p: P = P { x: 1 }; p.x += 2; }
    "#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("immutable"), "err: {err}");
}

#[test]
fn if_then_else_assigns_ok() {
    let src = r#"
        fn main() {
            let mut flag: bool = true;
            if flag { flag = false; } else { flag = true; }
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

// ===== Return & never type tests =====

#[test]
fn return_simple_ok() {
    let src = r#"fn f() -> i32 { return 1; }"#;
    match analyze_src(src) {
        Ok(_) => {}
        Err(e) => panic!("unexpected error: {e}"),
    }
}

#[test]
fn return_early_in_if_branch_ok() {
    // then branch returns early => else branch type determines whole if expression
    let src = r#"
        fn f(b: bool) -> i32 {
            if b { return 1; } else { 2 }
        }
    "#;
    match analyze_src(src) {
        Ok(_) => {}
        Err(e) => panic!("unexpected error: {e}"),
    }
}

#[test]
fn return_early_in_else_branch_ok() {
    let src = r#"
        fn f(b: bool) -> i32 {
            if b { 2 } else { return 1; }
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn both_branches_return_ok() {
    let src = r#"
        fn f(b: bool) -> i32 {
            if b { return 1; } else { return 2; }
        }
    "#; // function body diverges after if (both branches return) -> accepted
    assert!(analyze_src(src).is_ok());
}

#[test]
fn return_with_value_type_mismatch_function_decl_error() {
    let src = r#"fn f() -> i32 { return true; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected i32, found bool"), "err: {err}");
}

#[test]
fn tail_expression_unified_with_never_ok() {
    let src = r#"
        fn f(b: bool) -> i32 {
            if b { return 1; } else { 3 }
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn nested_if_with_return_unification_ok() {
    let src = r#"
        fn f(a: bool, b: bool) -> i32 {
            if a { if b { return 1; } else { return 2; } } else { 5 }
        }
    "#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn return_without_value_type_mismatch_error() {
    let src = r#"fn f() -> i32 { return; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected i32, found ()"), "err: {err}");
}

#[test]
fn return_with_value_in_unit_function_error() {
    let src = r#"fn f() { return 1; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("expected (), found <int>"), "err: {err}");
}

#[test]
fn block_trailing_semicolon_discards_value_ok() {
    // The inner block ends with an expression statement `1;` whose value is discarded, so block type is ()
    let src = r#"fn f() { { 1; }; }"#; // outer function returns () implicitly
    assert!(analyze_src(src).is_ok());
}

#[test]
fn block_last_statement_diverging_propagates_never_ok() {
    // Both branches return; last statement is if-expression whose type is Never, so block type is Never
    let src = r#"fn f(b: bool) -> i32 { if b { return 1; } else { return 2; } }"#;
    match analyze_src(src) {
        Ok(_) => {}
        Err(e) => panic!("unexpected error: {e}"),
    }
}

// ===== Loop / Break / Continue tests =====

#[test]
fn while_loop_basic_ok() {
    let src = r#"fn main() { let mut i: i32 = 0; while i < 3 { i = i + 1; } }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn loop_with_break_value_ok() {
    let src = r#"fn main() { let mut i: i32 = 0; let v: i32 = loop { if i == 3 { break i; } i = i + 1; }; }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn loop_with_unreachable_inconsistent_break_types_ok() {
    // Second break is after a guaranteed break in earlier statement sequence -> unreachable, so no error.
    let src = r#"fn main() { let mut i: i32 = 0; let v: i32 = loop { break 1; break true; }; }"#;
    assert!(analyze_src(src).is_ok());
}

#[test]
fn loop_with_inconsistent_break_types_error() {
    let src = r#"fn main() { let mut i: i32 = 0; let v: i32 = loop { if i == 3 { break true } else { break 1 } }; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("type mismatch"), "err: {err}");
}

#[test]
fn while_break_with_value_error() {
    let src = r#"fn main() { while true { break 1; } }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("break with value"), "err: {err}");
}

#[test]
fn break_outside_loop_error() {
    let src = r#"fn main() { break; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("break outside loop"), "err: {err}");
}

#[test]
fn continue_outside_loop_error() {
    let src = r#"fn main() { continue; }"#;
    let err = analyze_src(src).unwrap_err();
    assert!(err.contains("continue outside loop"), "err: {err}");
}

#[test]
fn deref_semantic_ok() {
    let src = r#"
            fn main() { let mut x: i32 = 10; let r: &i32 = &x; let y: i32 = *r; }
        "#;
    let result = analyze_src(src);
    assert!(result.is_ok(), "deref of &i32 should yield i32");
}

#[test]
fn deref_non_ref_error() {
    let src = r#"
            fn main() { let x: i32 = 5; let y = *x; }
        "#;
    let result = analyze_src(src);
    assert!(result.is_err(), "cannot deref non-reference");
}
