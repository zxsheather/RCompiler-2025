use std::usize;

use crate::frontend::{
    r_lexer::token::{Token, TokenType},
    r_parser::{
        ast::*,
        error::{ParseError, ParseResult},
    },
};

pub struct Parser {
    tokens: Vec<Token>,
    index: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, index: 0 }
    }

    pub fn parse(&mut self) -> ParseResult<Vec<AstNode>> {
        let mut nodes = Vec::new();
        while !self.is_end() {
            if self.check_type(&TokenType::Semicolon) {
                self.advance();
                continue;
            }

            nodes.push(self.next_node()?);

            if self.check_type(&TokenType::Eof) {
                break;
            }
        }
        Ok(nodes)
    }

    pub fn next_node(&mut self) -> ParseResult<AstNode> {
        match self.current_token().token_type {
            TokenType::Fn => Ok(AstNode::Function(self.parse_function()?)),
            _ => Ok(AstNode::Statement(self.parse_statement()?)),
        }
    }

    fn parse_function(&mut self) -> ParseResult<FunctionNode> {
        let fn_token = self.expect_type(&TokenType::Fn)?;
        let name = self.expect_type(&TokenType::Identifier)?;
        let param_list = self.parse_param_list()?;
        let return_type = if self.check_type(&TokenType::RArrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };
        let body = self.parse_block()?;
        Ok(FunctionNode {
            fn_token,
            name,
            param_list,
            return_type,
            body,
        })
    }

    fn parse_type(&mut self) -> ParseResult<TypeNode> {
        let token = self.current_token().clone();
        let res = match token.token_type {
            TokenType::I32 => Ok(TypeNode::I32(token)),
            TokenType::U32 => Ok(TypeNode::U32(token)),
            TokenType::ISize => Ok(TypeNode::ISize(token)),
            TokenType::USize => Ok(TypeNode::USize(token)),
            TokenType::F32 => Ok(TypeNode::F32(token)),
            TokenType::F64 => Ok(TypeNode::F64(token)),
            TokenType::Bool => Ok(TypeNode::Bool(token)),
            _ => Err(ParseError::Generic {
                message: format!("Expected a type, found {:?}", token.token_type),
                line: token.position.line,
                column: token.position.column,
            }),
        };
        self.advance();
        res
    }

    fn parse_block(&mut self) -> ParseResult<BlockNode> {
        let mut statements = Vec::new();
        let mut final_expr = None;
        self.expect_type(&TokenType::LBrace)?;
        while !self.check_type(&TokenType::RBrace) && !self.is_end() {
            if self.is_stat_start() {
                statements.push(self.parse_statement()?);
            } else {
                let expr = self.parse_expression()?;
                if self.check_type(&TokenType::Semicolon) {
                    self.advance();
                    statements.push(StatementNode::Expression(ExprStatementNode {
                        expression: expr,
                    }));
                } else {
                    final_expr = Some(expr);
                    break;
                }
            }
        }
        self.expect_type(&TokenType::RBrace)?;
        Ok(BlockNode {
            stats: statements,
            final_expr,
        })
    }

    fn is_stat_start(&self) -> bool {
        // Currently, only 'let' and simple assignments are forced statements
        match self.current_token().token_type {
            TokenType::Let => true,
            TokenType::Identifier => {
                self.peek_safe()
                    .map(|t| matches!(t.token_type, TokenType::Eq))
                    .unwrap_or(false)
            }
            _ => false,
        }
    }

    fn parse_statement(&mut self) -> ParseResult<StatementNode> {
        match self.current_token().token_type {
            TokenType::Let => {
                let let_token = self.expect_type(&TokenType::Let)?;
                let identifier = self.expect_type(&TokenType::Identifier)?;

                let type_annotation = if self.check_type(&TokenType::Colon) {
                    self.advance();
                    Some(self.parse_type()?)
                } else {
                    None
                };

                self.expect_type(&TokenType::Eq)?;
                let value = self.parse_expression()?;
                self.expect_type(&TokenType::Semicolon)?;

                Ok(StatementNode::Let(LetStatementNode {
                    let_token,
                    identifier,
                    type_annotation,
                    value,
                }))
            }
            TokenType::Identifier => {
                if self.peek_safe().map(|t| matches!(t.token_type, TokenType::Eq)).unwrap_or(false) {
                    let identifier = self.expect_type(&TokenType::Identifier)?;
                    self.expect_type(&TokenType::Eq)?;
                    let value = self.parse_expression()?;
                    self.expect_type(&TokenType::Semicolon)?;
                    Ok(StatementNode::Assign(AssignStatementNode { identifier, value }))
                } else {
                    let expression = self.parse_expression()?;
                    self.expect_type(&TokenType::Semicolon)?;
                    Ok(StatementNode::Expression(ExprStatementNode { expression }))
                }
            }
            _ => {
                let expression = self.parse_expression()?;
                self.expect_type(&TokenType::Semicolon)?;
                Ok(StatementNode::Expression(ExprStatementNode { expression }))
            }
        }
    }

    fn parse_expression(&mut self) -> ParseResult<ExpressionNode> {
        self.parse_expr_bp(0)
    }

    fn parse_expr_bp(&mut self, min_bp: u8) -> ParseResult<ExpressionNode> {
        // Parse prefix/primary
        let mut lhs = match self.current_token().token_type {
            TokenType::Plus | TokenType::Minus | TokenType::Not | TokenType::Tilde => {
                let op = self.current_token().clone();
                let r_bp = 25; // prefix binds tighter than multiplicative
                self.advance();
                let rhs = self.parse_expr_bp(r_bp)?;
                ExpressionNode::Unary(UnaryExprNode {
                    operator: op,
                    operand: Box::new(rhs),
                })
            }
            TokenType::If => self.parse_if_expression()?,
            TokenType::While => self.parse_while_expression()?,
            TokenType::LParen => {
                self.advance();
                let expr = self.parse_expression()?;
                self.expect_type(&TokenType::RParen)?;
                expr
            }
            TokenType::Identifier => {
                let tok = self.current_token().clone();
                self.advance();
                ExpressionNode::Identifier(tok)
            }
            TokenType::IntegerLiteral => {
                let tok = self.current_token().clone();
                self.advance();
                ExpressionNode::IntegerLiteral(tok)
            }
            TokenType::FloatLiteral => {
                let tok = self.current_token().clone();
                self.advance();
                ExpressionNode::FloatLiteral(tok)
            }
            TokenType::StringLiteral => {
                let tok = self.current_token().clone();
                self.advance();
                ExpressionNode::StringLiteral(tok)
            }
            TokenType::True | TokenType::False => {
                let tok = self.current_token().clone();
                self.advance();
                ExpressionNode::BoolLiteral(tok)
            }
            _ => {
                let token = self.current_token();
                return Err(ParseError::Generic {
                    message: format!("Unexpected token in expression: {:?}", token.token_type),
                    line: token.position.line,
                    column: token.position.column,
                });
            }
        };

        loop {
            // Function call as postfix operator: highest precedence
            if self.check_type(&TokenType::LParen) {
                let args = self.parse_argument_list()?;
                lhs = ExpressionNode::Call(CallExprNode {
                    function: Box::new(lhs),
                    args,
                });
                continue;
            }

            let op_tok = self.current_token().clone();
            let (lbp, rbp) = match self.infix_binding_power(&op_tok.token_type) {
                Some(bp) => bp,
                None => break,
            };
            if lbp < min_bp {
                break;
            }

            self.advance();
            let rhs = self.parse_expr_bp(rbp)?;
            lhs = ExpressionNode::Binary(BinaryExprNode {
                left_operand: Box::new(lhs),
                operator: op_tok,
                right_operand: Box::new(rhs),
            });
        }

        Ok(lhs)
    }

    fn infix_binding_power(&self, tt: &TokenType) -> Option<(u8, u8)> {
        // Return (left_bp, right_bp) pairs. Left associative by default.
        let lbp = match tt {
            TokenType::OrOr => 1,
            TokenType::AndAnd => 3,
            TokenType::Or => 5,
            TokenType::Xor => 7,
            TokenType::And => 9,
            TokenType::EqEq | TokenType::NEq => 11,
            TokenType::Lt | TokenType::LEq | TokenType::Gt | TokenType::GEq => 13,
            TokenType::SL | TokenType::SR => 15,
            TokenType::Plus | TokenType::Minus => 17,
            TokenType::Mul | TokenType::Div | TokenType::Percent => 19,
            _ => return None,
        };
        Some((lbp, lbp + 1))
    }

    fn parse_argument_list(&mut self) -> ParseResult<Vec<ExpressionNode>> {
        let mut args = Vec::new();
        self.expect_type(&TokenType::LParen)?;
        if self.check_type(&TokenType::RParen) {
            self.advance();
            return Ok(args);
        }
        loop {
            let expr = self.parse_expression()?;
            args.push(expr);
            if self.check_type(&TokenType::Comma) {
                self.advance();
                continue;
            }
            self.expect_type(&TokenType::RParen)?;
            break;
        }
        Ok(args)
    }

    fn parse_if_expression(&mut self) -> ParseResult<ExpressionNode> {
        let if_token = self.expect_type(&TokenType::If)?;
        let condition = self.parse_expression()?;
        let then_block = self.parse_block()?;
        let else_block = if self.check_type(&TokenType::Else) {
            self.advance();
            if self.check_type(&TokenType::If) {
                let nested = self.parse_if_expression()?;
                if let ExpressionNode::If(inner) = nested {
                    Some(ElseBodyNode::If(inner))
                } else {
                    unreachable!("parse_if_expression must return If variant");
                }
            } else {
                let blk = self.parse_block()?;
                Some(ElseBodyNode::Block(Box::new(blk)))
            }
        } else {
            None
        };
        Ok(ExpressionNode::If(Box::new(IfExprNode {
            if_token,
            condition,
            then_block,
            else_block,
        })))
    }

    fn parse_while_expression(&mut self) -> ParseResult<ExpressionNode> {
        let while_token = self.expect_type(&TokenType::While)?;
        let condition = self.parse_expression()?;
        let body = self.parse_block()?;
        Ok(ExpressionNode::While(Box::new(WhileExprNode {
            while_token,
            condition,
            body,
        })))
    }

    fn parse_param_list(&mut self) -> ParseResult<ParamListNode> {
        let mut params = Vec::new();
        self.expect_type(&TokenType::LParen)?;
        if self.check_type(&TokenType::RParen) {
            self.advance();
            return Ok(ParamListNode { params });
        }
        loop {
            let param = self.parse_param()?;
            params.push(param);
            if self.check_type(&TokenType::Comma) {
                self.advance();
                continue;
            }
            self.expect_type(&TokenType::RParen)?;
            break;
        }
        Ok(ParamListNode { params })
    }

    fn parse_param(&mut self) -> ParseResult<ParamNode> {
        let name = self.expect_type(&TokenType::Identifier)?;
        let type_annotation = if self.check_type(&TokenType::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };
        Ok(ParamNode {
            name,
            type_annotation,
        })
    }

    fn is_end(&self) -> bool {
        self.index >= self.tokens.len()
    }

    fn current_token(&self) -> &Token {
        self.tokens.get(self.index).expect("Index out or range")
    }

    fn peek(&self) -> &Token {
        self.tokens.get(self.index + 1).expect("Index out of range")
    }

    fn peek_n(&self, n: usize) -> &Token {
        self.tokens.get(self.index + n).expect("Index out of range")
    }

    fn peek_safe(&self) -> Option<&Token> {
        self.tokens.get(self.index + 1)
    }

    fn advance(&mut self) {
        self.index += 1;
    }

    fn advance_n(&mut self, n: usize) {
        self.index += n;
    }

    fn check_type(&mut self, token_type: &TokenType) -> bool {
        std::mem::discriminant(&self.current_token().token_type)
            == std::mem::discriminant(token_type)
    }

    fn expect_type(&mut self, token_type: &TokenType) -> ParseResult<Token> {
        if self.check_type(token_type) {
            let token = self.current_token().clone();
            self.advance();
            Ok(token)
        } else {
            let token = self.current_token();
            Err(ParseError::Generic {
                message: format!("Expected {:?}, found {:?}", token_type, token.token_type),
                line: token.position.line,
                column: token.position.column,
            })
        }
    }
}
