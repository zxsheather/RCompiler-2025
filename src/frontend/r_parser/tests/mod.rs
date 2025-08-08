use crate::frontend::r_lexer::lexer::Lexer;
use crate::frontend::r_lexer::token::{TokenType};
use crate::frontend::r_parser::ast::*;
use crate::frontend::r_parser::parser::Parser;

fn parse_expr(input: &str) -> ExpressionNode {
    // Ensure it's an expression statement for top-level parsing
    let mut src = input.trim_end().to_string();
    if !src.ends_with(';') {
        src.push(';');
    }
    let mut lexer = Lexer::new(src).expect("lexer init");
    let tokens = lexer.tokenize().expect("lex");
    let mut parser = Parser::new(tokens);
    match parser.parse().expect("parse").pop().expect("node") {
        AstNode::Expression(expr) => expr,
        AstNode::Statement(StatementNode::Expression(ExprStatementNode { expression })) => expression,
        other => panic!("expected expression, got {:?}", other),
    }
}

fn parse_nodes(input: &str) -> Vec<AstNode> {
    let mut lexer = Lexer::new(input.to_string()).expect("lexer init");
    let tokens = lexer.tokenize().expect("lex");
    let mut parser = Parser::new(tokens);
    parser.parse().expect("parse")
}

#[test]
fn precedence_multiplicative_over_additive() {
    // 1 + 2 * 3 => +(1, *(2,3))
    let expr = parse_expr("1 + 2 * 3");
    match expr {
        ExpressionNode::Binary(BinaryExprNode { operator, left_operand, right_operand }) => {
            assert!(matches!(operator.token_type, TokenType::Plus));
            match (*right_operand).clone() {
                ExpressionNode::Binary(BinaryExprNode { operator, left_operand, right_operand }) => {
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
        ExpressionNode::Binary(BinaryExprNode { operator, left_operand, right_operand }) => {
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
        ExpressionNode::Binary(BinaryExprNode { operator, left_operand, right_operand }) => {
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
