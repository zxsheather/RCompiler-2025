use crate::frontend::r_lexer::lexer::Lexer;
use crate::frontend::r_lexer::token::TokenType;
use crate::frontend::r_parser::ast::*;
use crate::frontend::r_parser::parser::Parser;
use std::env;
use std::fs;
use std::path::PathBuf;

fn current_test_name() -> String {
    std::thread::current()
        .name()
        .map(|s| s.to_string())
        .unwrap_or_else(|| "unknown_test".to_string())
}

fn sanitize_filename(s: &str) -> String {
    s.chars()
        .map(|c| match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '-' | '_' => c,
            _ => '_',
        })
        .collect()
}

fn maybe_dump_json(nodes: &[AstNode]) {
    if let Ok(dir) = env::var("AST_JSON_DIR") {
        let name = sanitize_filename(&current_test_name());
        let mut path = PathBuf::from(dir);
        let _ = fs::create_dir_all(&path);
        path.push(format!("{}.json", name));
        if let Ok(s) = serde_json::to_string_pretty(nodes) {
            let _ = fs::write(path, s);
        }
    }
}

fn parse_expr(input: &str) -> ExpressionNode {
    // Ensure it's an expression statement for top-level parsing
    let mut src = input.trim_end().to_string();
    if !src.ends_with(';') {
        src.push(';');
    }
    let mut lexer = Lexer::new(src).expect("lexer init");
    let tokens = lexer.tokenize().expect("lex");
    let mut parser = Parser::new(tokens);
    let mut ast = parser.parse().expect("parse");
    maybe_dump_json(&ast);
    match ast.pop().expect("node") {
        AstNode::Expression(expr) => expr,
        AstNode::Statement(StatementNode::Expression(ExprStatementNode { expression })) => {
            expression
        }
        other => panic!("expected expression, got {:?}", other),
    }
}

fn parse_nodes(input: &str) -> Vec<AstNode> {
    let mut lexer = Lexer::new(input.to_string()).expect("lexer init");
    let tokens = lexer.tokenize().expect("lex");
    let mut parser = Parser::new(tokens);
    let ast = parser.parse().expect("parse");
    maybe_dump_json(&ast);
    ast
}

#[test]
fn precedence_multiplicative_over_additive() {
    // 1 + 2 * 3 => +(1, *(2,3))
    let expr = parse_expr("1 + 2 * 3");
    match expr {
        ExpressionNode::Binary(BinaryExprNode {
            operator,
            left_operand,
            right_operand,
        }) => {
            assert!(matches!(operator.token_type, TokenType::Plus));
            match (*right_operand).clone() {
                ExpressionNode::Binary(BinaryExprNode {
                    operator,
                    left_operand,
                    right_operand,
                }) => {
                    assert!(matches!(operator.token_type, TokenType::Mul));
                    assert!(matches!(*left_operand, ExpressionNode::IntegerLiteral(_)));
                    assert!(matches!(*right_operand, ExpressionNode::IntegerLiteral(_)));
                }
                _ => panic!("right should be a Mul"),
            }
            assert!(matches!(*left_operand, ExpressionNode::IntegerLiteral(_)));
        }
        _ => panic!("expected binary expr"),
    }
}

#[test]
fn left_associative_addition() {
    // 1 - 2 - 3 => (- (- 1 2) 3)
    let expr = parse_expr("1 - 2 - 3");
    match expr {
        ExpressionNode::Binary(BinaryExprNode {
            operator,
            left_operand,
            right_operand,
        }) => {
            assert!(matches!(operator.token_type, TokenType::Minus));
            // Left should be another minus
            match *left_operand {
                ExpressionNode::Binary(BinaryExprNode { operator, .. }) => {
                    assert!(matches!(operator.token_type, TokenType::Minus));
                }
                _ => panic!("left should be a minus"),
            }
            assert!(matches!(*right_operand, ExpressionNode::IntegerLiteral(_)));
        }
        _ => panic!("expected binary expr"),
    }
}

#[test]
fn function_call_binds_tight() {
    let expr = parse_expr("f(1, 2) + 3");
    match expr {
        ExpressionNode::Binary(BinaryExprNode {
            operator,
            left_operand,
            right_operand,
        }) => {
            assert!(matches!(operator.token_type, TokenType::Plus));
            match *left_operand {
                ExpressionNode::Call(CallExprNode { function, args }) => {
                    match *function {
                        ExpressionNode::Identifier(ref tok) => assert_eq!(tok.lexeme, "f"),
                        _ => panic!("call callee should be identifier"),
                    }
                    assert_eq!(args.len(), 2);
                }
                _ => panic!("left should be call"),
            }
            assert!(matches!(*right_operand, ExpressionNode::IntegerLiteral(_)));
        }
        _ => panic!("expected binary expr"),
    }
}

#[test]
fn let_and_assign_statements() {
    let nodes = parse_nodes("{ let x: i32 = 1 + 2 * 3; x = x + 1; };");
    assert_eq!(nodes.len(), 1);
    assert!(matches!(
        nodes[0],
        AstNode::Statement(StatementNode::Expression(ExprStatementNode { .. }))
    ));
}

#[test]
fn if_else_expression() {
    let nodes = parse_nodes("if 1 < 2 { 1 } else { 2 };");
    assert_eq!(nodes.len(), 1);
    assert!(matches!(
        nodes[0],
        AstNode::Statement(StatementNode::Expression(ExprStatementNode { .. }))
    ));
}

#[test]
fn array_literal_and_indexing() {
    // Array literal
    let expr = parse_expr("[1, 2, 3][0]");
    match expr {
        ExpressionNode::Index(IndexExprNode { array, index }) => {
            assert!(matches!(*index, ExpressionNode::IntegerLiteral(_)));
            match *array {
                ExpressionNode::ArrayLiteral(elems) => {
                    assert_eq!(elems.elements.len(), 3);
                    assert!(matches!(
                        elems.elements[0],
                        ExpressionNode::IntegerLiteral(_)
                    ));
                }
                _ => panic!("expected array literal"),
            }
        }
        _ => panic!("expected index expression"),
    }
}

#[test]
fn array_type_parsing_in_fn_param() {
    let src = "fn f(a: [i32; 3]) { a[1]; }";
    let nodes = parse_nodes(src);
    assert_eq!(nodes.len(), 1);
    match &nodes[0] {
        AstNode::Function(func) => {
            assert_eq!(func.param_list.params.len(), 1);
            let p = &func.param_list.params[0];
            match p.type_annotation.as_ref().unwrap() {
                TypeNode::Array { elem_type, size } => {
                    match **elem_type {
                        TypeNode::I32(_) => {}
                        _ => panic!("elem type should be i32"),
                    }
                    assert!(matches!(size, Some(_)));
                }
                _ => panic!("expected array type"),
            }
        }
        _ => panic!("expected function"),
    }
}

#[test]
fn index_with_arbitrary_expression() {
    // a[i + 1];
    let expr = parse_expr("a[i + 1]");
    match expr {
        ExpressionNode::Index(IndexExprNode { array, index }) => {
            assert!(matches!(*array, ExpressionNode::Identifier(_)));
            match *index {
                ExpressionNode::Binary(BinaryExprNode {
                    operator,
                    left_operand,
                    right_operand,
                }) => {
                    assert!(matches!(operator.token_type, TokenType::Plus));
                    assert!(matches!(*left_operand, ExpressionNode::Identifier(_)));
                    assert!(matches!(*right_operand, ExpressionNode::IntegerLiteral(_)));
                }
                _ => panic!("index should be a binary expr i+1"),
            }
        }
        _ => panic!("expected index expression"),
    }

    // f(x)[g(y) * 2];
    let expr2 = parse_expr("f(x)[g(y) * 2]");
    match expr2 {
        ExpressionNode::Index(IndexExprNode { array, index }) => {
            // array side is a call f(x)
            match *array {
                ExpressionNode::Call(_) => {}
                _ => panic!("expected call on array side"),
            }
            match *index {
                ExpressionNode::Binary(BinaryExprNode {
                    operator,
                    left_operand,
                    right_operand,
                }) => {
                    assert!(matches!(operator.token_type, TokenType::Mul));
                    match *left_operand {
                        ExpressionNode::Call(_) => {}
                        _ => panic!("left of * should be a call g(y)"),
                    }
                    assert!(matches!(*right_operand, ExpressionNode::IntegerLiteral(_)));
                }
                _ => panic!("index should be a binary expr g(y)*2"),
            }
        }
        _ => panic!("expected index expression"),
    }
}

#[test]
fn assignment_right_associative_in_expr() {
    let nodes = parse_nodes("a = b = 1;");
    assert_eq!(nodes.len(), 1);
    match &nodes[0] {
        AstNode::Statement(StatementNode::Assign(assign)) => {
            // RHS should be a binary '=' with rhs = int 1
            match &assign.value {
                ExpressionNode::Binary(BinaryExprNode {
                    operator,
                    left_operand,
                    right_operand,
                }) => {
                    assert!(matches!(operator.token_type, TokenType::Eq));
                    // left of inner '=' should be identifier 'b'
                    assert!(matches!(&**left_operand, ExpressionNode::Identifier(_)));
                    assert!(matches!(
                        &**right_operand,
                        ExpressionNode::IntegerLiteral(_)
                    ));
                }
                _ => panic!("assign RHS should be an assignment expression"),
            }
        }
        other => panic!("expected assignment statement, got {:?}", other),
    }
}

#[test]
fn assignment_has_lowest_precedence() {
    let nodes = parse_nodes("a = b + c * d;");
    assert_eq!(nodes.len(), 1);
    match &nodes[0] {
        AstNode::Statement(StatementNode::Assign(assign)) => match &assign.value {
            ExpressionNode::Binary(BinaryExprNode {
                operator,
                left_operand,
                right_operand,
            }) => {
                assert!(matches!(operator.token_type, TokenType::Plus));
                assert!(matches!(&**left_operand, ExpressionNode::Identifier(_)));
                match &**right_operand {
                    ExpressionNode::Binary(BinaryExprNode { operator, .. }) => {
                        assert!(matches!(operator.token_type, TokenType::Mul));
                    }
                    _ => panic!("expected multiplicative on right of plus"),
                }
            }
            _ => panic!("RHS should be binary +"),
        },
        other => panic!("expected assignment statement, got {:?}", other),
    }
}

#[test]
fn multi_dimension_array() {
    let nodes = parse_nodes("let a: [[i32; 2]; 3] = [[1, 2], [3, 4], [5, 6]];");
    assert_eq!(nodes.len(), 1);
}
