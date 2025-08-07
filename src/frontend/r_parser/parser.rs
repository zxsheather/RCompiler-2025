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
            nodes.push(self.next_node()?);
            self.advance();
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
        true
    }

    fn parse_statement(&mut self) -> ParseResult<StatementNode> {}

    fn parse_expression(&mut self) -> ParseResult<ExpressionNode> {}

    fn parse_param_list(&mut self) -> ParseResult<ParamListNode> {}

    fn parse_type_annotation(&mut self) -> ParseResult<Param> {}

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
