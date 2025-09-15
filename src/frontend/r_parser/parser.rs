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
            TokenType::Trait => Ok(AstNode::Trait(self.parse_trait_decl()?)),
            TokenType::Struct => Ok(AstNode::Struct(self.parse_struct_delc()?)),
            TokenType::Fn => Ok(AstNode::Function(self.parse_function()?)),
            TokenType::Impl => {
                if let Some(tok) = self.peek_n_safe(2) {
                    if matches!(tok.token_type, TokenType::For) {
                        Ok(AstNode::ImplTrait(self.parse_impl_trait_block()?))
                    } else {
                        Ok(AstNode::Impl(self.parse_impl_block()?))
                    }
                } else {
                    Ok(AstNode::Impl(self.parse_impl_block()?))
                }
            }
            _ => Ok(AstNode::Statement(self.parse_statement()?)),
        }
    }

    fn parse_trait_decl(&mut self) -> ParseResult<TraitDeclNode> {
        let trait_token = self.expect_type(&TokenType::Trait)?;
        let name = self.expect_type(&TokenType::Identifier)?;
        self.expect_type(&TokenType::LBrace)?;
        let mut methods = Vec::new();
        while !self.check_type(&TokenType::RBrace) {
            let fn_token = self.expect_type(&TokenType::Fn)?;
            let method_name = self.expect_type(&TokenType::Identifier)?;
            let params = self.parse_param_list()?;
            let return_type = if self.check_type(&TokenType::RArrow) {
                self.advance();
                Some(self.parse_type()?)
            } else {
                None
            };
            self.expect_type(&TokenType::Semicolon)?;
            methods.push(TraitMethodSigNode {
                fn_token,
                name: method_name,
                param_list: params,
                return_type,
            });
        }
        self.expect_type(&TokenType::RBrace)?;
        Ok(TraitDeclNode {
            trait_token,
            name,
            methods,
        })
    }

    fn parse_impl_trait_block(&mut self) -> ParseResult<ImplTraitBlockNode> {
        let impl_token = self.expect_type(&TokenType::Impl)?;
        let trait_name = self.expect_type(&TokenType::Identifier)?;
        let for_token = self.expect_type(&TokenType::For)?;
        let type_name = self.expect_type(&TokenType::Identifier)?;
        self.expect_type(&TokenType::LBrace)?;
        let mut methods = Vec::new();
        while !self.check_type(&TokenType::RBrace) {
            let mut method = self.parse_function()?;
            if let Some(first) = method.param_list.params.get_mut(0) {
                if std::mem::discriminant(&first.name.token_type)
                    == std::mem::discriminant(&TokenType::SelfLower)
                {
                    match &mut first.type_annotation {
                        Some(TypeNode::SelfRef { mutable }) => {
                            let concrete_type = if *mutable {
                                TypeNode::Ref {
                                    inner_type: Box::new(TypeNode::Named(type_name.clone())),
                                    mutable: true,
                                }
                            } else {
                                TypeNode::Ref {
                                    inner_type: Box::new(TypeNode::Named(type_name.clone())),
                                    mutable: false,
                                }
                            };
                            first.type_annotation = Some(concrete_type);
                        }
                        None => {
                            first.type_annotation = Some(TypeNode::Named(type_name.clone()));
                        }
                        _ => {}
                    }
                }
            }
            methods.push(method);
        }
        self.expect_type(&TokenType::RBrace)?;
        Ok(ImplTraitBlockNode {
            impl_token,
            trait_name,
            for_token,
            type_name,
            methods,
        })
    }

    fn parse_const_item(&mut self) -> ParseResult<ConstItemNode> {
        let const_token = self.expect_type(&TokenType::Const)?;
        let name = self.expect_type(&TokenType::Identifier)?;
        self.expect_type(&TokenType::Colon)?;
        let type_annotation = self.parse_type()?;
        self.expect_type(&TokenType::Eq)?;
        let value = self.parse_expression()?;
        Ok(ConstItemNode {
            const_token,
            name,
            type_annotation,
            value,
        })
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
            TokenType::And => {
                self.advance();
                let mutable = if self.check_type(&TokenType::Mut) {
                    self.advance();
                    true
                } else {
                    false
                };
                if self.check_type(&TokenType::SelfLower) {
                    self.advance();
                    Ok(TypeNode::SelfRef { mutable })
                } else {
                    let inner_type = self.parse_type()?;
                    Ok(TypeNode::Ref {
                        inner_type: Box::new(inner_type),
                        mutable,
                    })
                }
            }
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
            TokenType::StringType => {
                self.advance();
                Ok(TypeNode::String(token))
            }
            TokenType::StrType => {
                self.advance();
                Ok(TypeNode::Str(token))
            }
            TokenType::CharType => {
                self.advance();
                Ok(TypeNode::Char(token))
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
                    Some(Box::new(self.parse_expression()?))
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
        if final_expr.is_none() {
            if let Some(last_stat) = statements.last() {
                if let StatementNode::Expression(ExprStatementNode { expression }) = last_stat {
                    if let ExpressionNode::If(_)
                    | ExpressionNode::While(_)
                    | ExpressionNode::Loop(_) = expression
                    {
                        final_expr = Some(expression.clone());
                        statements.pop();
                    }
                }
            }
        }
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
            TokenType::Let | TokenType::If | TokenType::While | TokenType::Loop => true,
            TokenType::Return => true,
            TokenType::Const | TokenType::Fn => true,
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
                let identifier =
                    self.expect_multi_types(&[TokenType::Identifier, TokenType::Underscore])?;

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
            TokenType::If => {
                let expression = self.parse_if_expression()?;
                Ok(StatementNode::Expression(ExprStatementNode { expression }))
            }
            TokenType::While => {
                let expression = self.parse_while_expression()?;
                Ok(StatementNode::Expression(ExprStatementNode { expression }))
            }
            TokenType::Loop => {
                let expression = self.parse_loop_expression()?;
                Ok(StatementNode::Expression(ExprStatementNode { expression }))
            }
            TokenType::Return => {
                let expression = self.parse_return_expression()?;
                if self.check_type(&TokenType::Semicolon) {
                    self.advance();
                }
                Ok(StatementNode::Expression(ExprStatementNode { expression }))
            }
            TokenType::Const => {
                let const_item = self.parse_const_item()?;
                self.expect_type(&TokenType::Semicolon)?;
                Ok(StatementNode::Const(const_item))
            }
            TokenType::Fn => {
                let func = self.parse_function()?;
                Ok(StatementNode::Func(func))
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
                let r_bp = 135; // prefix binds tighter than multiplicative
                self.advance();
                let rhs = self.parse_expr_bp(r_bp)?;
                ExpressionNode::Unary(UnaryExprNode {
                    operator: op,
                    operand: Box::new(rhs),
                })
            }
            TokenType::And => {
                self.advance();
                let mutable = if self.check_type(&TokenType::Mut) {
                    self.advance();
                    true
                } else {
                    false
                };
                let r_bp = 135;
                let rhs = self.parse_expr_bp(r_bp)?;
                ExpressionNode::Ref(RefExprNode {
                    mutable,
                    operand: Box::new(rhs),
                })
            }
            TokenType::Mul => {
                let star = self.current_token().clone();
                let r_bp = 135;
                self.advance();
                let rhs = self.parse_expr_bp(r_bp)?;
                ExpressionNode::Deref(DerefExprNode {
                    star_token: star,
                    operand: Box::new(rhs),
                })
            }
            TokenType::If => self.parse_if_expression()?,
            TokenType::While => self.parse_while_expression()?,
            TokenType::Loop => self.parse_loop_expression()?,
            TokenType::Break => self.parse_break_expression()?,
            TokenType::Continue => self.parse_continue_expression()?,
            TokenType::Return => self.parse_return_expression()?,
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
            TokenType::StringType
                if self.peek_safe().map(|t| t.token_type) == Some(TokenType::ColonColon) =>
            {
                let tok = self.current_token().clone();
                self.advance();
                self.advance();
                let member = self.expect_type(&TokenType::Identifier)?;
                ExpressionNode::StaticMember(StaticMemberExprNode {
                    type_name: tok,
                    member: member,
                })
            }
            TokenType::Identifier => {
                let tok = self.current_token().clone();
                self.advance();

                if self.check_type(&TokenType::ColonColon) {
                    self.advance();
                    let member = self.expect_type(&TokenType::Identifier)?;
                    ExpressionNode::StaticMember(StaticMemberExprNode {
                        type_name: tok,
                        member: member,
                    })
                } else if self.check_type(&TokenType::LBrace) {
                    let is_struct_literal = if let Some(t1) = self.peek_safe() {
                        if !matches!(t1.token_type, TokenType::Identifier) {
                            false
                        } else if let Some(t2) = self.peek_n_safe(2) {
                            matches!(t2.token_type, TokenType::Colon | TokenType::Comma)
                        } else {
                            false
                        }
                    } else {
                        false
                    };
                    if is_struct_literal {
                        let fields = self.parse_struct_literal_fields()?;
                        ExpressionNode::StructLiteral(StructLiteralNode { name: tok, fields })
                    } else {
                        ExpressionNode::Identifier(tok)
                    }
                } else {
                    ExpressionNode::Identifier(tok)
                }
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
            TokenType::CharLiteral => {
                let tok = self.current_token().clone();
                self.advance();
                ExpressionNode::CharLiteral(tok)
            }
            TokenType::Underscore => {
                let tok = self.current_token().clone();
                self.advance();
                ExpressionNode::Underscore(tok)
            }
            TokenType::True | TokenType::False => {
                let tok = self.current_token().clone();
                self.advance();
                ExpressionNode::BoolLiteral(tok)
            }
            TokenType::SelfLower => {
                let tok = self.current_token().clone();
                self.advance();
                ExpressionNode::Identifier(tok)
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
                lhs = match lhs {
                    ExpressionNode::Member(MemberExprNode { object, field }) => {
                        ExpressionNode::MethodCall(MethodCallExprNode {
                            object: object.clone(),
                            method: field.clone(),
                            args,
                        })
                    }
                    other => ExpressionNode::Call(CallExprNode {
                        function: Box::new(other),
                        args,
                    }),
                };
                continue;
            }

            if self.check_type(&TokenType::As) {
                let as_token = self.expect_type(&TokenType::As)?;
                let type_name = self.parse_type()?;
                lhs = ExpressionNode::As(Box::new(AsExprNode {
                    expr: Box::new(lhs),
                    as_token,
                    type_name,
                }));
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
            TokenType::Eq
            | TokenType::PlusEq
            | TokenType::MinusEq
            | TokenType::MulEq
            | TokenType::DivEq
            | TokenType::ModEq
            | TokenType::AndEq
            | TokenType::OrEq
            | TokenType::XorEq => Some((10, 9)),
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
        // if self.check_type(&TokenType::RParen) {
        //     self.advance();
        //     return Ok(args);
        // }
        loop {
            if self.check_type(&TokenType::RParen) {
                self.advance();
                return Ok(args);
            }
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
        self.expect_type(&TokenType::LBrace)?;
        let mut fields = Vec::new();
        loop {
            if self.check_type(&TokenType::RBrace) {
                self.advance();
                return Ok(fields);
            }
            let name = self.expect_type(&TokenType::Identifier)?;
            let value = if self.check_type(&TokenType::Colon) {
                self.advance();
                self.parse_expression()?
            } else {
                ExpressionNode::Identifier(name.clone())
            };
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

    fn parse_impl_block(&mut self) -> ParseResult<ImplNode> {
        let impl_token = self.expect_type(&TokenType::Impl)?;
        let name = self.expect_type(&TokenType::Identifier)?;
        self.expect_type(&TokenType::LBrace)?;
        let mut methods = Vec::new();
        while !self.check_type(&TokenType::RBrace) {
            let mut method = self.parse_function()?;
            if let Some(first) = method.param_list.params.get_mut(0) {
                if std::mem::discriminant(&first.name.token_type)
                    == std::mem::discriminant(&TokenType::SelfLower)
                {
                    match &mut first.type_annotation {
                        Some(TypeNode::SelfRef { mutable }) => {
                            let concrete_type = if *mutable {
                                TypeNode::Ref {
                                    inner_type: Box::new(TypeNode::Named(name.clone())),
                                    mutable: true,
                                }
                            } else {
                                TypeNode::Ref {
                                    inner_type: Box::new(TypeNode::Named(name.clone())),
                                    mutable: false,
                                }
                            };
                            first.type_annotation = Some(concrete_type);
                        }
                        None => {
                            first.type_annotation = Some(TypeNode::Named(name.clone()));
                        }
                        _ => {}
                    }
                }
            }
            methods.push(method);
        }
        self.expect_type(&TokenType::RBrace)?;
        Ok(ImplNode {
            impl_token,
            name,
            methods,
        })
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

    fn parse_loop_expression(&mut self) -> ParseResult<ExpressionNode> {
        let loop_token = self.expect_type(&TokenType::Loop)?;
        let body = self.parse_block()?;
        Ok(ExpressionNode::Loop(Box::new(LoopExprNode {
            loop_token,
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
        // Support forms:
        // 1. (mut) name [: Type]
        // 2. (mut) self [: Type]
        // 3. &(mut) self (later desugar -> self: &(mut) Struct)
        if self.check_type(&TokenType::And) {
            self.advance();
            let mutable = if self.check_type(&TokenType::Mut) {
                self.advance();
                true
            } else {
                false
            };
            let self_tok = self.expect_type(&TokenType::SelfLower)?;
            return Ok(ParamNode {
                name: self_tok,
                type_annotation: Some(TypeNode::SelfRef { mutable }),
                mutable: false,
            });
        }
        let mutable = if self.check_type(&TokenType::Mut) {
            self.advance();
            true
        } else {
            false
        };

        let name = if self.check_type(&TokenType::Identifier) {
            self.expect_type(&TokenType::Identifier)?
        } else if self.check_type(&TokenType::SelfLower) {
            self.expect_type(&TokenType::SelfLower)?
        } else {
            let token = self.current_token();
            return Err(ParseError::Generic {
                message: format!("Expected parameter name, found {:?}", token.token_type),
                line: token.position.line,
                column: token.position.column,
            });
        };
        let type_annotation = if self.check_type(&TokenType::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };
        Ok(ParamNode {
            name,
            type_annotation,
            mutable,
        })
    }

    fn parse_break_expression(&mut self) -> ParseResult<ExpressionNode> {
        let break_token = self.expect_type(&TokenType::Break)?;
        if self.check_type(&TokenType::Semicolon) {
            self.advance();
            return Ok(ExpressionNode::Break(Box::new(BreakExprNode {
                break_token,
                value: None,
            })));
        }
        let value = self.parse_expression()?;
        Ok(ExpressionNode::Break(Box::new(BreakExprNode {
            break_token,
            value: Some(value),
        })))
    }

    fn parse_continue_expression(&mut self) -> ParseResult<ExpressionNode> {
        let continue_token = self.expect_type(&TokenType::Continue)?;
        Ok(ExpressionNode::Continue(Box::new(ContinueExprNode {
            continue_token,
        })))
    }

    fn parse_return_expression(&mut self) -> ParseResult<ExpressionNode> {
        let return_token = self.expect_type(&TokenType::Return)?;
        if self.check_type(&TokenType::Semicolon) {
            return Ok(ExpressionNode::Return(Box::new(ReturnExprNode {
                return_token,
                value: None,
            })));
        }
        let value = self.parse_expression()?;
        Ok(ExpressionNode::Return(Box::new(ReturnExprNode {
            return_token,
            value: Some(value),
        })))
    }

    fn parse_array_literal(&mut self) -> ParseResult<ArrayLiteralNode> {
        self.expect_type(&TokenType::LBracket)?;
        let mut elements = Vec::new();
        if self.check_type(&TokenType::RBracket) {
            self.advance();
            return Ok(ArrayLiteralNode::Elements { elements });
        }
        // Lookahead for repeat form: <expr> ; <IntegerLiteral> ]
        let first_expr = self.parse_expression()?;
        if self.check_type(&TokenType::Semicolon) {
            self.advance();
            let size = self.parse_expression()?;
            self.expect_type(&TokenType::RBracket)?;
            return Ok(ArrayLiteralNode::Repeated {
                element: Box::new(first_expr),
                size: Box::new(size),
            });
        } else {
            elements.push(first_expr);
            while self.check_type(&TokenType::Comma) {
                self.advance();
                if self.check_type(&TokenType::RBracket) {
                    break;
                }
                let expr = self.parse_expression()?;
                elements.push(expr);
            }
            self.expect_type(&TokenType::RBracket)?;
        }
        Ok(ArrayLiteralNode::Elements { elements })
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

    fn peek_n_safe(&self, n: usize) -> Option<&Token> {
        self.tokens.get(self.index + n)
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

    fn expect_multi_types(&mut self, token_types: &[TokenType]) -> ParseResult<Token> {
        for tt in token_types {
            if self.check_type(tt) {
                let token = self.current_token().clone();
                self.advance();
                return Ok(token);
            }
        }
        let token = self.current_token();
        Err(ParseError::Generic {
            message: format!(
                "Expected one of {:?}, found {:?}",
                token_types, token.token_type
            ),
            line: token.position.line,
            column: token.position.column,
        })
    }
}
