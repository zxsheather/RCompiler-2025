use std::{collections::HashMap, usize};

use crate::frontend::{
    r_lexer::token::{Token, TokenType},
    r_parser::ast::{
        AssignStatementNode, AstNode, BinaryExprNode, BlockNode, CallExprNode, ElseBodyNode,
        ExprStatementNode, ExpressionNode, FunctionNode, IfExprNode, IndexExprNode,
        LetStatementNode, MemberExprNode, StatementNode, StructLiteralNode, TupleLiteralNode,
        TypeNode, UnaryExprNode, WhileExprNode,
    },
    r_semantic::{
        error::{SemanticError, SemanticResult},
        types::RxType,
    },
};

#[derive(Debug, Clone, PartialEq)]
pub struct Symbol {
    pub name: String,
    pub ty: RxType,
    pub mutable: bool,
    pub token: Token,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Scope {
    vars: HashMap<String, Symbol>,
}

impl Scope {
    fn declare_var(&mut self, symbol: Symbol) {
        self.vars.insert(symbol.name.clone(), symbol);
    }

    fn get(&self, name: &str) -> Option<&Symbol> {
        self.vars.get(name)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncSig {
    param_types: Vec<RxType>,
    return_type: RxType,
    token: Token,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Globe {
    scope_stack: Vec<Scope>,
    funcs: HashMap<String, FuncSig>,
    structs: HashMap<String, HashMap<String, RxType>>,
}

impl Globe {
    fn push_scope(&mut self) {
        self.scope_stack.push(Scope::default());
    }

    fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }

    fn declare_var(&mut self, symbol: Symbol) -> SemanticResult<()> {
        if let Some(scope) = self.scope_stack.last_mut() {
            scope.declare_var(symbol);
            Ok(())
        } else {
            Err(SemanticError::DeclarationOutOfScope {
                name: symbol.name,
                line: symbol.token.position.line,
                column: symbol.token.position.column,
            })
        }
    }

    fn lookup_var(&self, name: &str) -> Option<&Symbol> {
        for scope in self.scope_stack.iter().rev() {
            if let Some(s) = scope.get(name) {
                return Some(s);
            }
        }
        None
    }

    fn declare_fn(
        &mut self,
        name: String,
        params: Vec<RxType>,
        ret: RxType,
        tok: Token,
    ) -> SemanticResult<()> {
        if self.funcs.contains_key(&name) {
            return Err(SemanticError::FunctionRedeclaration {
                name: name.clone(),
                line: tok.position.line,
                column: tok.position.column,
            });
        }
        self.funcs.insert(
            name,
            FuncSig {
                param_types: params,
                return_type: ret,
                token: tok,
            },
        );
        Ok(())
    }

    fn lookup_fn(&self, name: &str) -> Option<&FuncSig> {
        self.funcs.get(name)
    }
}

pub struct Analyzer {
    pub globe: Globe,
}

impl Analyzer {
    pub fn new() -> Self {
        Self {
            globe: Globe::default(),
        }
    }

    pub fn analyse_program(&mut self, nodes: &[AstNode]) -> SemanticResult<()> {
        for node in nodes {
            match node {
                AstNode::Function(func) => {
                    let name = func.name.lexeme.clone();
                    let params: Vec<RxType> = func
                        .param_list
                        .params
                        .iter()
                        .map(|p| self.type_from_ann(p.type_annotation.as_ref(), &p.name))
                        .collect::<SemanticResult<Vec<_>>>()?;
                    let ret = match &func.return_type {
                        Some(t) => self.type_from_node(t)?,
                        None => RxType::Unit,
                    };

                    let _ = self.globe.declare_fn(name, params, ret, func.name.clone());
                }
                AstNode::Struct(sd) => {
                    let mut field_map = HashMap::new();
                    for field in &sd.fields {
                        let ty = self.type_from_node(&field.type_annotation)?;
                        field_map.insert(field.name.lexeme.clone(), ty);
                    }
                    self.globe.structs.insert(sd.name.lexeme.clone(), field_map);
                }
                _ => {
                    // Do nothing in this pass
                }
            }
        }

        for node in nodes {
            match node {
                AstNode::Function(func) => {
                    self.analyse_function(func)?;
                }

                AstNode::Statement(stmt) => {
                    self.globe.push_scope();
                    self.analyse_statement(stmt)?;
                    self.globe.pop_scope();
                }

                AstNode::Expression(expr) => {
                    self.globe.push_scope();
                    self.analyse_expression(expr)?;
                    self.globe.pop_scope();
                }

                AstNode::Struct(_) => {
                    // Nothing to do in this pass
                }
            }
        }
        Ok(())
    }

    pub fn analyse_function(&mut self, func: &FunctionNode) -> SemanticResult<()> {
        self.globe.push_scope();
        let mut param_types = Vec::new();
        for param in &func.param_list.params {
            let ty = self.type_from_ann(param.type_annotation.as_ref(), &param.name)?;
            param_types.push(ty.clone());
            self.globe.declare_var(Symbol {
                name: param.name.lexeme.clone(),
                ty: ty,
                mutable: false,
                token: param.name.clone(),
            })?;
        }
        let ret_ty = func
            .return_type
            .as_ref()
            .map(|t| self.type_from_node(t))
            .transpose()?
            .unwrap_or(RxType::Unit);
        let blk_ty = self.analyse_block(&func.body)?;
        if ret_ty != blk_ty {
            return Err(SemanticError::FunctionReturnTypeMismatch {
                name: func.name.lexeme.clone(),
                expected: ret_ty,
                found: blk_ty,
                line: func.fn_token.position.line,
                column: func.fn_token.position.column,
            });
        }
        Ok(())
    }

    pub fn analyse_block(&mut self, blk: &BlockNode) -> SemanticResult<RxType> {
        self.globe.push_scope();
        for stmt in &blk.stats {
            self.analyse_statement(stmt)?;
        }
        let ret = if let Some(expr) = &blk.final_expr {
            self.analyse_expression(expr)?
        } else {
            RxType::Unit
        };
        Ok(ret)
    }

    pub fn analyse_statement(&mut self, stmt: &StatementNode) -> SemanticResult<()> {
        match stmt {
            StatementNode::Let(LetStatementNode {
                let_token,
                mutable,
                identifier,
                type_annotation,
                value,
            }) => {
                let expr_ty = self.analyse_expression(&value)?;
                if let Some(ty) = type_annotation {
                    let decl_ty = self.type_from_node(&ty)?;
                    if decl_ty != expr_ty {
                        return Err(SemanticError::AssignTypeMismatched {
                            expected: decl_ty,
                            found: expr_ty,
                            line: let_token.position.line,
                            column: let_token.position.column,
                        });
                    }
                }
                self.globe.declare_var(Symbol {
                    ty: expr_ty,
                    name: identifier.lexeme.clone(),
                    mutable: *mutable,
                    token: identifier.clone(),
                })?;
                Ok(())
            }
            StatementNode::Assign(AssignStatementNode { identifier, value }) => {
                let symbol = match self.globe.lookup_var(&identifier.lexeme).cloned() {
                    Some(s) => s,
                    None => {
                        return Err(SemanticError::UndefinedIdentifier {
                            name: identifier.lexeme.clone(),
                            line: identifier.position.line,
                            column: identifier.position.column,
                        });
                    }
                };

                if !symbol.mutable {
                    return Err(SemanticError::AssignImmutableVar {
                        name: identifier.lexeme.clone(),
                        line: identifier.position.line,
                        column: identifier.position.column,
                    });
                }

                let value_ty = self.analyse_expression(value)?;
                if value_ty != symbol.ty {
                    return Err(SemanticError::AssignTypeMismatched {
                        expected: symbol.ty,
                        found: value_ty,
                        line: identifier.position.line,
                        column: identifier.position.column,
                    });
                }
                Ok(())
            }
            StatementNode::Expression(ExprStatementNode { expression }) => {
                self.analyse_expression(expression)?;
                Ok(())
            }
        }
    }

    pub fn analyse_expression(&mut self, expr: &ExpressionNode) -> SemanticResult<RxType> {
        match expr {
            ExpressionNode::Identifier(token) => {
                if let Some(symbol) = self.globe.lookup_var(&token.lexeme) {
                    Ok(symbol.ty.clone())
                } else {
                    Err(SemanticError::UndefinedIdentifier {
                        name: token.lexeme.clone(),
                        line: token.position.line,
                        column: token.position.column,
                    })
                }
            }
            ExpressionNode::IntegerLiteral(token) => {
                if token.lexeme.contains("isize") {
                    Ok(RxType::ISize)
                } else if token.lexeme.contains("usize") {
                    Ok(RxType::USize)
                } else if token.lexeme.contains("u32") {
                    Ok(RxType::U32)
                } else {
                    Ok(RxType::I32)
                }
            }
            ExpressionNode::StringLiteral(_) => Ok(RxType::String),
            ExpressionNode::BoolLiteral(_) => Ok(RxType::Bool),
            ExpressionNode::Block(b) => Ok(self.analyse_block(b)?),
            ExpressionNode::ArrayLiteral(arr) => {
                let elem_ty = if let Some(node) = arr.elements.first() {
                    self.analyse_expression(node)?
                } else {
                    RxType::Unit
                };
                for elem in arr.elements.iter() {
                    let tp = self.analyse_expression(elem)?;
                    if tp != elem_ty {
                        return Err(SemanticError::MixedTypedArray {
                            type1: elem_ty,
                            type2: tp,
                        });
                    }
                }
                Ok(RxType::Array(Box::new(elem_ty), Some(arr.elements.len())))
            }
            ExpressionNode::TupleLiteral(t) => {
                if t.elements.is_empty() {
                    Ok(RxType::Unit)
                } else {
                    let mut types = Vec::with_capacity(t.elements.len());
                    for elem in &t.elements {
                        types.push(self.analyse_expression(elem)?);
                    }
                    Ok(RxType::Tuple(types))
                }
            }
            ExpressionNode::Unary(u) => Ok(self.analyse_unary(u)?),
            ExpressionNode::Binary(b) => Ok(self.analyse_binary(b)?),
            ExpressionNode::Index(i) => Ok(self.analyse_index(i)?),
            ExpressionNode::If(i) => Ok(self.analyse_if(i)?),
            ExpressionNode::While(w) => Ok(self.analyse_while(w)?),
            ExpressionNode::Call(c) => Ok(self.analyse_call(c)?),
            ExpressionNode::Member(m) => Ok(self.analyse_member(m)?),
            ExpressionNode::StructLiteral(s) => Ok(self.analyse_struct_literal(s)?),
        }
    }

    fn analyse_unary(&mut self, u: &UnaryExprNode) -> SemanticResult<RxType> {
        let rt = self.analyse_expression(&u.operand)?;
        match &u.operator.token_type {
            TokenType::Plus | TokenType::Minus => {
                if rt.is_integer() {
                    Err(SemanticError::InvalidUnaryOperandType {
                        expected_type: "numeric type".to_string(),
                        found_type: format!("{}", rt),
                        line: u.operator.position.line,
                        column: u.operator.position.column,
                    })
                } else {
                    Ok(rt)
                }
            }
            TokenType::Not => {
                if rt != RxType::Bool {
                    Err(SemanticError::InvalidUnaryOperandType {
                        expected_type: "bool".to_string(),
                        found_type: format!("{}", rt),
                        line: u.operator.position.line,
                        column: u.operator.position.column,
                    })
                } else {
                    Ok(RxType::Bool)
                }
            }
            _ => Err(SemanticError::UnsupportedUnaryOperation {
                op: format!("{}", u.operator.token_type),
                type_: format!("{}", rt),
                line: u.operator.position.line,
                column: u.operator.position.column,
            }),
        }
    }

    fn analyse_binary(&mut self, b: &BinaryExprNode) -> SemanticResult<RxType> {
        let lt = self.analyse_expression(&b.left_operand)?;
        let rt = self.analyse_expression(&b.right_operand)?;
        use TokenType::*;
        let op_token = b.operator.token_type;
        let line = b.operator.position.line;
        let column = b.operator.position.column;
        match op_token {
            Plus | Minus | Mul | Div | Percent | And | Or | Xor => {
                if !lt.is_integer() {
                    Err(SemanticError::ArityMismatch {
                        operator: op_token.as_str().to_string(),
                        expected_type: "numeric type".to_string(),
                        found: lt,
                        line,
                        column,
                    })
                } else if lt != rt {
                    Err(SemanticError::MismatchedBinaryTypes {
                        op: op_token.as_str().to_string(),
                        left: lt,
                        right: rt,
                        line,
                        column,
                    })
                } else {
                    Ok(lt)
                }
            }

            EqEq | NEq | Lt | LEq | Gt | GEq => {
                if !lt.is_integer() {
                    Err(SemanticError::ArityMismatch {
                        operator: op_token.as_str().to_string(),
                        expected_type: "numeric type".to_string(),
                        found: lt,
                        line,
                        column,
                    })
                } else if lt != rt {
                    Err(SemanticError::MismatchedBinaryTypes {
                        op: op_token.as_str().to_string(),
                        left: lt,
                        right: rt,
                        line,
                        column,
                    })
                } else {
                    Ok(RxType::Bool)
                }
            }

            AndAnd | OrOr => {
                if lt != RxType::Bool || rt != RxType::Bool {
                    Err(SemanticError::InvalidLogicalTypes {
                        left: lt,
                        right: rt,
                        line,
                        column,
                    })
                } else {
                    Ok(RxType::Bool)
                }
            }

            Eq => {
                if let ExpressionNode::Identifier(token) = &*b.left_operand {
                    let Some(symbol) = self.globe.lookup_var(&token.lexeme) else {
                        return Err(SemanticError::UndefinedIdentifier {
                            name: token.lexeme.clone(),
                            line,
                            column,
                        });
                    };
                    if !symbol.mutable {
                        return Err(SemanticError::AssignImmutableVar {
                            name: token.lexeme.clone(),
                            line,
                            column,
                        });
                    }

                    if rt != symbol.ty {
                        return Err(SemanticError::AssignTypeMismatched {
                            expected: symbol.ty.clone(),
                            found: rt,
                            line,
                            column,
                        });
                    }

                    Ok(symbol.ty.clone())
                } else {
                    Err(SemanticError::InvalidLValueType { line, column })
                }
            }
            _ => Err(SemanticError::Generic {
                msg: "Unsupported binary operator".to_string(),
                line,
                column,
            }),
        }
    }

    fn analyse_index(&mut self, i: &IndexExprNode) -> SemanticResult<RxType> {
        let arr_ty = self.analyse_expression(&i.array)?;
        let idx_ty = self.analyse_expression(&i.index)?;
        if !idx_ty.is_integer() {
            // Currently not handle position information
            return Err(SemanticError::InvalidIndexType {
                found: idx_ty,
                line: 0,
                column: 0,
            });
        }
        if let RxType::Array(elem, _) = arr_ty {
            Ok(*elem)
        } else {
            Err(SemanticError::IndexNonArray {
                found: arr_ty,
                line: 0,
                column: 0,
            })
        }
    }

    fn analyse_member(&mut self, m: &MemberExprNode) -> SemanticResult<RxType> {
        let obj_ty = self.analyse_expression(&m.object)?;
        let line = m.field.position.line;
        let column = m.field.position.column;
        let RxType::Struct(name) = obj_ty else {
            return Err(SemanticError::Generic {
                msg: format!("Member access requires struct, found {}", obj_ty),
                line,
                column,
            });
        };
        let Some(field_map) = self.globe.structs.get(&name) else {
            return Err(SemanticError::UnknownStruct { name, line, column });
        };
        let Some(ty) = field_map.get(&m.field.lexeme) else {
            return Err(SemanticError::UnknownStructField {
                name,
                field: m.field.lexeme.clone(),
                line,
                column,
            });
        };
        Ok(ty.clone())
    }

    fn analyse_struct_literal(&mut self, s: &StructLiteralNode) -> SemanticResult<RxType> {
        let name = s.name.lexeme.clone();
        let line = s.name.position.line;
        let column = s.name.position.column;
        let Some(field_map) = self.globe.structs.get(&name).cloned() else {
            return Err(SemanticError::UnknownStruct { name, line, column });
        };
        for field in s.fields.iter() {
            let found = self.analyse_expression(&field.value)?;
            let Some(expected) = field_map.get(&field.name.lexeme) else {
                return Err(SemanticError::UnknownStructField {
                    name: s.name.lexeme.clone(),
                    field: field.name.lexeme.clone(),
                    line,
                    column,
                });
            };
            if found != *expected {
                return Err(SemanticError::StructFieldTypeMismatch {
                    name: s.name.lexeme.clone(),
                    field: field.name.lexeme.clone(),
                    expected: expected.clone(),
                    found,
                    line,
                    column,
                });
            }
        }
        Ok(RxType::Struct(s.name.lexeme.clone()))
    }

    fn analyse_if(&mut self, i: &IfExprNode) -> SemanticResult<RxType> {
        let line = i.if_token.position.line;
        let column = i.if_token.position.column;
        let cond_ty = self.analyse_expression(&i.condition)?;
        if cond_ty != RxType::Bool {
            return Err(SemanticError::InvalidConditionType {
                found: cond_ty,
                line,
                column,
            });
        }
        let then_ty = self.analyse_block(&i.then_block)?;
        let else_ty = match &i.else_block {
            Some(ElseBodyNode::Block(b)) => Some(self.analyse_block(b)?),
            Some(ElseBodyNode::If(i)) => Some(self.analyse_if(i)?),
            None => None,
        };
        if let Some(elty) = else_ty {
            if elty != then_ty {
                Err(SemanticError::BranchTypeMismatched {
                    then_ty,
                    else_ty: elty,
                    line,
                    column,
                })
            } else {
                Ok(then_ty)
            }
        } else {
            Ok(then_ty)
        }
    }

    fn analyse_while(&mut self, w: &WhileExprNode) -> SemanticResult<RxType> {
        let line = w.while_token.position.line;
        let column = w.while_token.position.column;
        let cond_ty = self.analyse_expression(&w.condition)?;
        if cond_ty != RxType::Bool {
            return Err(SemanticError::InvalidConditionType {
                found: cond_ty,
                line,
                column,
            });
        }
        self.analyse_block(&w.body)?;
        Ok(RxType::Unit)
    }

    fn analyse_call(&mut self, c: &CallExprNode) -> SemanticResult<RxType> {
        let callee_name = if let ExpressionNode::Identifier(token) = &*c.function {
            token.lexeme.clone()
        } else {
            // Only support simple function call, and currently not handle the position information
            return Err(SemanticError::Generic {
                msg: "Only simple function call supported".to_string(),
                line: 0,
                column: 0,
            });
        };

        let Some(sig) = self.globe.lookup_fn(&callee_name).cloned() else {
            return Err(SemanticError::UnknownCallee {
                name: callee_name,
                line: 0,
                column: 0,
            });
        };

        let line = sig.token.position.line;
        let column = sig.token.position.column;
        if sig.param_types.len() != c.args.len() {
            return Err(SemanticError::ArgsNumMismatched {
                callee: callee_name,
                expected: sig.param_types.len(),
                found: c.args.len(),
                line,
                column,
            });
        }

        for (i, (pt, arg)) in sig.param_types.iter().zip(&c.args).enumerate() {
            let at = self.analyse_expression(arg)?;
            if *pt != at {
                return Err(SemanticError::ArgTypeMismatched {
                    callee: callee_name,
                    index: i,
                    expected: pt.clone(),
                    found: at.clone(),
                    line,
                    column,
                });
            }
        }
        Ok(sig.return_type)
    }

    fn type_from_ann(&self, ann: Option<&TypeNode>, name_tok: &Token) -> SemanticResult<RxType> {
        match ann {
            Some(t) => self.type_from_node(t),
            None => Err(SemanticError::NeedAnnotation {
                name: name_tok.lexeme.clone(),
                line: name_tok.position.line,
                column: name_tok.position.column,
            }),
        }
    }

    fn type_from_node(&self, type_node: &TypeNode) -> SemanticResult<RxType> {
        Ok(match type_node {
            TypeNode::I32(_) => RxType::I32,
            TypeNode::U32(_) => RxType::U32,
            TypeNode::ISize(_) => RxType::ISize,
            TypeNode::USize(_) => RxType::USize,
            TypeNode::Bool(_) => RxType::Bool,
            TypeNode::String(_) => RxType::String,
            TypeNode::Unit => RxType::Unit,
            TypeNode::Tuple(tys) => {
                let mut rxtypes = Vec::with_capacity(tys.len());
                for ty in tys {
                    rxtypes.push(self.type_from_node(ty)?);
                }
                RxType::Tuple(rxtypes)
            }
            TypeNode::Array { elem_type, size } => {
                let elem_ty = self.type_from_node(&elem_type)?;
                let len = if let Some(tok) = size {
                    tok.lexeme.parse::<usize>().ok()
                } else {
                    None
                };
                RxType::Array(Box::new(elem_ty), len)
            }
            TypeNode::Named(token) => {
                let name = token.lexeme.clone();
                if self.globe.structs.contains_key(&name) {
                    RxType::Struct(name)
                } else {
                    return Err(SemanticError::UnknownType {
                        name,
                        line: token.position.line,
                        column: token.position.column,
                    });
                }
            }
        })
    }
}
