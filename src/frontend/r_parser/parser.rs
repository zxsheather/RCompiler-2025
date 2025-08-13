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

            if self.check_type(&TokenType::Eof) {
                break;
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
            TokenType::Struct => Ok(AstNode::Struct(self.parse_struct_delc()?)),
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
        match token.token_type {
            TokenType::I32 => {
                self.advance();
                Ok(TypeNode::I32(token))
            }
            TokenType::U32 => {
                self.advance();
                Ok(TypeNode::U32(token))
            }
            TokenType::ISize => {
                self.advance();
                Ok(TypeNode::ISize(token))
            }
            TokenType::USize => {
                self.advance();
                Ok(TypeNode::USize(token))
            }
            TokenType::Bool => {
                self.advance();
                Ok(TypeNode::Bool(token))
            }
            TokenType::Identifier => {
                self.advance();
                Ok(TypeNode::Named(token))
            }
            TokenType::LBracket => {
                // [T; N] or [T]
                self.advance();
                let elem_type = self.parse_type()?;
                let size = if self.check_type(&TokenType::Semicolon) {
                    self.advance();
                    Some(self.expect_type(&TokenType::IntegerLiteral)?)
                } else {
                    None
                };
                self.expect_type(&TokenType::RBracket)?;
                Ok(TypeNode::Array {
                    elem_type: Box::new(elem_type),
                    size,
                })
            }
            // tuple
            TokenType::LParen => {
                self.advance();
                if self.check_type(&TokenType::RParen) {
                    self.advance();
                    return Ok(TypeNode::Unit);
                }
                let first = self.parse_type()?;
                if self.check_type(&TokenType::Comma) {
                    let mut elems = vec![first];
                    while self.check_type(&TokenType::Comma) {
                        self.advance();
                        if self.check_type(&TokenType::RParen) {
                            break;
                        }
                        let ty = self.parse_type()?;
                        elems.push(ty);
                    }
                    self.expect_type(&TokenType::RParen)?;
                    Ok(TypeNode::Tuple(elems))
                } else {
                    self.expect_type(&TokenType::RParen)?;
                    Ok(first)
                }
            }
            _ => Err(ParseError::Generic {
                message: format!("Expected a type, found {:?}", token.token_type),
                line: token.position.line,
                column: token.position.column,
            }),
        }
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

    fn parse_struct_delc(&mut self) -> ParseResult<StructDeclNode> {
        let struct_token = self.expect_type(&TokenType::Struct)?;
        let name = self.expect_type(&TokenType::Identifier)?;
        self.expect_type(&TokenType::LBrace)?;
        let mut fields = Vec::new();
        while !self.check_type(&TokenType::RBrace) {
            let field_name = self.expect_type(&TokenType::Identifier)?;
            self.expect_type(&TokenType::Colon)?;
            let field_type = self.parse_type()?;
            fields.push(StructFieldNode {
                name: field_name,
                type_annotation: field_type,
            });
            if self.check_type(&TokenType::Comma) {
                self.advance();
            }
        }
        self.expect_type(&TokenType::RBrace)?;
        Ok(StructDeclNode {
            struct_token,
            name,
            fields,
        })
    }

    fn is_stat_start(&self) -> bool {
        // Currently, only 'let' and simple assignments are forced statements
        match self.current_token().token_type {
            TokenType::Let => true,
            TokenType::Identifier => self
                .peek_safe()
                .map(|t| matches!(t.token_type, TokenType::Eq))
                .unwrap_or(false),
            _ => false,
        }
    }

    fn parse_statement(&mut self) -> ParseResult<StatementNode> {
        match self.current_token().token_type {
            TokenType::Let => {
                let let_token = self.expect_type(&TokenType::Let)?;
                let mutable = self.check_type(&TokenType::Mut);
                if mutable {
                    self.advance();
                }
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
                    mutable,
                    identifier,
                    type_annotation,
                    value,
                }))
            }
            TokenType::Identifier => {
                if self
                    .peek_safe()
                    .map(|t| matches!(t.token_type, TokenType::Eq))
                    .unwrap_or(false)
                {
                    let identifier = self.expect_type(&TokenType::Identifier)?;
                    self.expect_type(&TokenType::Eq)?;
                    let value = self.parse_expression()?;
                    self.expect_type(&TokenType::Semicolon)?;
                    Ok(StatementNode::Assign(AssignStatementNode {
                        identifier,
                        value,
                    }))
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
            TokenType::LBrace => {
                let block = self.parse_block()?;
                ExpressionNode::Block(Box::new(block))
            }
            TokenType::LBracket => ExpressionNode::ArrayLiteral(self.parse_array_literal()?),
            TokenType::LParen => {
                self.advance();
                if self.check_type(&TokenType::RParen) {
                    self.advance();
                    ExpressionNode::TupleLiteral(TupleLiteralNode {
                        elements: Vec::new(),
                    })
                } else {
                    let first_expr = self.parse_expression()?;
                    if self.check_type(&TokenType::Comma) {
                        let mut elems = vec![first_expr];
                        while self.check_type(&TokenType::Comma) {
                            self.advance();
                            if self.check_type(&TokenType::RParen) {
                                break;
                            }
                            let expr = self.parse_expression()?;
                            elems.push(expr);
                        }
                        self.expect_type(&TokenType::RParen)?;
                        ExpressionNode::TupleLiteral(TupleLiteralNode { elements: elems })
                    } else {
                        self.expect_type(&TokenType::RParen)?;
                        first_expr
                    }
                }
            }
            TokenType::Identifier => {
                let tok = self.current_token().clone();
                self.advance();
                if self.check_type(&TokenType::LBrace) {
                    if self.tokens.len() > self.index + 2 {
                        let t1 = self.peek().token_type;
                        let t2 = self.peek_n(2).token_type;
                        if matches!(t1, TokenType::Identifier) && matches!(t2, TokenType::Colon) {
                            let fields = self.parse_struct_literal_fields()?;
                            return Ok(ExpressionNode::StructLiteral(StructLiteralNode {
                                name: tok,
                                fields,
                            }));
                        }
                    }
                }
                ExpressionNode::Identifier(tok)
            }
            TokenType::IntegerLiteral => {
                let tok = self.current_token().clone();
                self.advance();
                ExpressionNode::IntegerLiteral(tok)
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

        // Postfix and infix
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

            if self.check_type(&TokenType::LBracket) {
                self.advance();
                let index = self.parse_expression()?;
                self.expect_type(&TokenType::RBracket)?;
                lhs = ExpressionNode::Index(IndexExprNode {
                    array: Box::new(lhs),
                    index: Box::new(index),
                });
                continue;
            }

            if self.check_type(&TokenType::Dot) {
                self.advance();
                let field = self.expect_type(&TokenType::Identifier)?;
                lhs = ExpressionNode::Member(MemberExprNode {
                    object: Box::new(lhs),
                    field,
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
        // Return (left_bp, right_bp) pairs.
        match tt {
            TokenType::Eq => Some((10, 9)),
            TokenType::OrOr => Some((30, 31)),
            TokenType::AndAnd => Some((40, 41)),
            TokenType::Or => Some((50, 51)),
            TokenType::Xor => Some((60, 61)),
            TokenType::And => Some((70, 71)),
            TokenType::EqEq | TokenType::NEq => Some((80, 81)),
            TokenType::Lt | TokenType::LEq | TokenType::Gt | TokenType::GEq => Some((90, 91)),
            TokenType::SL | TokenType::SR => Some((100, 101)),
            TokenType::Plus | TokenType::Minus => Some((110, 111)),
            TokenType::Mul | TokenType::Div | TokenType::Percent => Some((120, 121)),
            _ => return None,
        }
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

    fn parse_struct_literal_fields(&mut self) -> ParseResult<Vec<StructLiteralFieldNode>> {
        self.expect_type(&TokenType::LBrace);
        let mut fields = Vec::new();
        if self.check_type(&TokenType::RBrace) {
            self.advance();
            return Ok(fields);
        }
        loop {
            let name = self.expect_type(&TokenType::Identifier)?;
            self.expect_type(&TokenType::Colon);
            let value = self.parse_expression()?;
            fields.push(StructLiteralFieldNode { name, value });
            if self.check_type(&TokenType::Comma) {
                self.advance();
                continue;
            }
            self.expect_type(&TokenType::RBrace)?;
            break;
        }
        Ok(fields)
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

    fn parse_array_literal(&mut self) -> ParseResult<ArrayLiteralNode> {
        self.expect_type(&TokenType::LBracket)?;
        let mut elements = Vec::new();
        if self.check_type(&TokenType::RBracket) {
            self.advance();
            return Ok(ArrayLiteralNode { elements });
        }
        loop {
            let expr = self.parse_expression()?;
            elements.push(expr);
            if self.check_type(&TokenType::Comma) {
                self.advance();
                continue;
            }
            self.expect_type(&TokenType::RBracket)?;
            break;
        }
        Ok(ArrayLiteralNode { elements })
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
