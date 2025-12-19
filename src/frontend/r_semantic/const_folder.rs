use crate::frontend::{
    r_lexer::token::{Token, TokenType},
    r_parser::ast::{ArrayLiteralNode, BinaryExprNode, ExpressionNode, TypeNode, UnaryExprNode},
    r_semantic::{
        analyzer::Globe,
        error::{SemanticError, SemanticResult},
        tyctxt::TypeContext,
        types::{RxType, RxValue},
    },
};

pub struct ConstFolder;

impl ConstFolder {
    pub fn calc_expr(
        expr: &ExpressionNode,
        report_tok: &Token,
        globe: &Globe,
        type_context: &mut TypeContext,
    ) -> SemanticResult<(RxType, RxValue)> {
        match expr {
            ExpressionNode::IntegerLiteral(token, node_id) => {
                let res = Self::parse_int_literal(token)?;
                type_context.set_type(*node_id, res.0.clone());
                Ok(res)
            }
            ExpressionNode::StringLiteral(token, node_id) => {
                let s = token.lexeme.trim_matches('"').to_string();
                type_context.set_type(*node_id, RxType::String);
                Ok((RxType::String, RxValue::String(s)))
            }
            ExpressionNode::BoolLiteral(token, node_id) => {
                let v = match token.token_type {
                    TokenType::True => true,
                    TokenType::False => false,
                    _ => token.lexeme == "true",
                };
                type_context.set_type(*node_id, RxType::Bool);
                Ok((RxType::Bool, RxValue::Bool(v)))
            }
            ExpressionNode::CharLiteral(token, node_id) => {
                // Assume lexeme like 'a' or '\n'
                let ch = token
                    .lexeme
                    .trim_matches('"')
                    .trim_matches('\'')
                    .chars()
                    .next()
                    .unwrap_or('\0');
                type_context.set_type(*node_id, RxType::Char);
                Ok((RxType::Char, RxValue::Char(ch)))
            }
            ExpressionNode::ArrayLiteral(node) => match node {
                ArrayLiteralNode::Elements { elements, node_id } => {
                    let mut vals = Vec::new();
                    let mut elem_type = RxType::Never;
                    for elem in elements {
                        let (ty, val) = Self::calc_expr(elem, report_tok, globe, type_context)?;
                        if let Some(unified_ty) = RxType::unify(&elem_type, &ty) {
                            elem_type = unified_ty;
                            vals.push(val);
                        } else {
                            return Err(SemanticError::InvalidConstExpr {
                                expr: "array elements have mismatched types".to_string(),
                                line: report_tok.position.line,
                                column: report_tok.position.column,
                            });
                        }
                    }
                    let ty = RxType::Array(Box::new(elem_type.clone()), Some(vals.len()));
                    type_context.set_type(*node_id, ty.clone());
                    Ok((ty, RxValue::Array(elem_type, vals.len(), vals)))
                }
                ArrayLiteralNode::Repeated {
                    element,
                    size,
                    node_id,
                } => {
                    let (elem_ty, elem_val) =
                        Self::calc_expr(element, report_tok, globe, type_context)?;
                    let (size_ty, size_val) =
                        Self::calc_expr(size, report_tok, globe, type_context)?;
                    if RxType::unify(&size_ty, &RxType::USize).is_some() {
                        let size_usize = size_val.as_usize()?;
                        let vals = vec![elem_val; size_usize];
                        let ty = RxType::Array(Box::new(elem_ty.clone()), Some(size_usize));
                        type_context.set_type(*node_id, ty.clone());
                        type_context.set_array_layout(*node_id, elem_ty.clone(), Some(size_usize));
                        Ok((ty, RxValue::Array(elem_ty, size_usize, vals)))
                    } else {
                        Err(SemanticError::InvalidConstExpr {
                            expr: "array size must be usize".to_string(),
                            line: report_tok.position.line,
                            column: report_tok.position.column,
                        })
                    }
                }
            },
            ExpressionNode::Identifier(token, node_id) => {
                if let Some(val) = globe.lookup_const(&token.lexeme) {
                    type_context.set_type(*node_id, val.clone().0);
                    Ok(val.clone())
                } else {
                    Err(SemanticError::Generic {
                        msg: format!("Undefined constant {}", token.lexeme),
                        line: token.position.line,
                        column: token.position.column,
                    })
                }
            }
            ExpressionNode::Unary(UnaryExprNode {
                operator,
                operand,
                node_id,
            }) => {
                let (ty, val) = Self::calc_expr(operand, report_tok, globe, type_context)?;
                match operator.token_type {
                    TokenType::Minus => match (ty, val) {
                        (RxType::I32, RxValue::I32(v)) => {
                            type_context.set_type(*node_id, RxType::I32);
                            Ok((RxType::I32, RxValue::I32(-v)))
                        }
                        (RxType::ISize, RxValue::ISize(v)) => {
                            type_context.set_type(*node_id, RxType::ISize);
                            Ok((RxType::ISize, RxValue::ISize(-v)))
                        }
                        (RxType::IntLiteral, RxValue::IntLiteral(v)) => {
                            type_context.set_type(*node_id, RxType::IntLiteral);
                            Ok((RxType::IntLiteral, RxValue::IntLiteral(-v)))
                        }
                        (RxType::U32, RxValue::U32(_)) | (RxType::USize, RxValue::USize(_)) => {
                            Err(SemanticError::InvalidUnaryOperandType {
                                expected_type: "signed int".to_string(),
                                found_type: "unsigned int".to_string(),
                                line: report_tok.position.line,
                                column: report_tok.position.column,
                            })
                        }
                        (t, v) => Err(SemanticError::InvalidUnaryOperandType {
                            expected_type: "int-like".to_string(),
                            found_type: format!("{t:?}/{v:?}"),
                            line: report_tok.position.line,
                            column: report_tok.position.column,
                        }),
                    },
                    TokenType::Not => match (ty, val) {
                        (RxType::Bool, RxValue::Bool(v)) => {
                            type_context.set_type(*node_id, RxType::Bool);
                            Ok((RxType::Bool, RxValue::Bool(!v)))
                        }
                        _ => Err(SemanticError::InvalidUnaryOperandType {
                            expected_type: "bool".to_string(),
                            found_type: "non-bool".to_string(),
                            line: report_tok.position.line,
                            column: report_tok.position.column,
                        }),
                    },
                    _ => Err(SemanticError::Generic {
                        msg: format!("unsupported unary operator {:?}", operator.token_type),
                        line: report_tok.position.line,
                        column: report_tok.position.column,
                    }),
                }
            }
            ExpressionNode::Binary(BinaryExprNode {
                left_operand,
                operator,
                right_operand,
                node_id,
            }) => {
                let (lty, lval) = Self::calc_expr(left_operand, report_tok, globe, type_context)?;
                let (rty, rval) = Self::calc_expr(right_operand, report_tok, globe, type_context)?;
                let res = Self::eval_binary(lty, lval, rty, rval, operator, report_tok)?;
                type_context.set_type(*node_id, res.0.clone());
                Ok(res)
            }
            ExpressionNode::As(as_node) => {
                let (expr_ty, expr_val) =
                    Self::calc_expr(&as_node.expr, report_tok, globe, type_context)?;
                let target_ty = Self::type_from_node(&as_node.type_name, report_tok)?;
                let val = expr_val.as_int()?;
                match target_ty {
                    RxType::I32 => {
                        if val < i32::MIN as i64 || val > i32::MAX as i64 {
                            return Err(SemanticError::InvalidConstExpr {
                                expr: "integer overflow in as-cast to i32".to_string(),
                                line: report_tok.position.line,
                                column: report_tok.position.column,
                            });
                        }
                        type_context.set_type(as_node.node_id, RxType::I32);
                        Ok((RxType::I32, RxValue::I32(val as i32)))
                    }
                    RxType::U32 => {
                        if val < 0 || val > u32::MAX as i64 {
                            return Err(SemanticError::InvalidConstExpr {
                                expr: "integer overflow in as-cast to u32".to_string(),
                                line: report_tok.position.line,
                                column: report_tok.position.column,
                            });
                        }
                        type_context.set_type(as_node.node_id, RxType::U32);
                        Ok((RxType::U32, RxValue::U32(val as u32)))
                    }
                    RxType::ISize => {
                        if val < i32::MIN as i64 || val > i32::MAX as i64 {
                            return Err(SemanticError::InvalidConstExpr {
                                expr: "integer overflow in as-cast to isize".to_string(),
                                line: report_tok.position.line,
                                column: report_tok.position.column,
                            });
                        }
                        type_context.set_type(as_node.node_id, RxType::ISize);
                        Ok((RxType::ISize, RxValue::ISize(val as isize)))
                    }
                    RxType::USize => {
                        if val < 0 || val > u32::MAX as i64 {
                            return Err(SemanticError::InvalidConstExpr {
                                expr: "integer overflow in as-cast to usize".to_string(),
                                line: report_tok.position.line,
                                column: report_tok.position.column,
                            });
                        }
                        type_context.set_type(as_node.node_id, RxType::USize);
                        Ok((RxType::USize, RxValue::USize(val as usize)))
                    }
                    _ => Err(SemanticError::InvalidConstExpr {
                        expr: format!("unsupported as-cast from {expr_ty:?} to {target_ty:?}"),
                        line: report_tok.position.line,
                        column: report_tok.position.column,
                    }),
                }
            }
            other => Err(SemanticError::InvalidConstExpr {
                expr: format!("{other:?}"),
                line: report_tok.position.line,
                column: report_tok.position.column,
            }),
        }
    }

    pub fn parse_int_literal(token: &Token) -> SemanticResult<(RxType, RxValue)> {
        let mut clean = token.lexeme.replace('_', "");
        let ty = if clean.ends_with("isize") {
            clean.truncate(clean.len() - "isize".len());
            RxType::ISize
        } else if clean.ends_with("usize") {
            clean.truncate(clean.len() - "usize".len());
            RxType::USize
        } else if clean.ends_with("u32") {
            clean.truncate(clean.len() - "u32".len());
            RxType::U32
        } else if clean.ends_with("i32") {
            clean.truncate(clean.len() - "i32".len());
            RxType::I32
        } else {
            RxType::IntLiteral
        };

        let (base, digits) = if let Some(stripped) = clean.strip_prefix("0x") {
            (16, stripped)
        } else if let Some(stripped) = clean.strip_prefix("0b") {
            (2, stripped)
        } else if let Some(stripped) = clean.strip_prefix("0o") {
            (8, stripped)
        } else {
            (10, clean.as_str())
        };

        if digits.is_empty() {
            return Err(SemanticError::InvalidConstExpr {
                expr: token.lexeme.clone(),
                line: token.position.line,
                column: token.position.column,
            });
        }

        let parse_result = match ty {
            RxType::I32 => {
                i32::from_str_radix(digits, base).map(|v| (RxType::I32, RxValue::I32(v)))
            }
            RxType::U32 => {
                u32::from_str_radix(digits, base).map(|v| (RxType::U32, RxValue::U32(v)))
            }
            RxType::ISize => {
                isize::from_str_radix(digits, base).map(|v| (RxType::ISize, RxValue::ISize(v)))
            }
            RxType::USize => {
                usize::from_str_radix(digits, base).map(|v| (RxType::USize, RxValue::USize(v)))
            }
            RxType::IntLiteral => i64::from_str_radix(digits, base)
                .map(|v| (RxType::IntLiteral, RxValue::IntLiteral(v))),
            _ => unreachable!(),
        };

        parse_result.map_err(|_| SemanticError::InvalidConstExpr {
            expr: token.lexeme.clone(),
            line: token.position.line,
            column: token.position.column,
        })
    }

    fn eval_binary(
        lty: RxType,
        lval: RxValue,
        rty: RxType,
        rval: RxValue,
        op_tok: &Token,
        report_tok: &Token,
    ) -> SemanticResult<(RxType, RxValue)> {
        use TokenType::*;
        // Helper to coerce IntLiteral to other side type
        let coerce_pair = |lty: RxType,
                           lval: RxValue,
                           rty: RxType,
                           rval: RxValue|
         -> (RxType, RxValue, RxType, RxValue) {
            match (&lty, &rty, &lval, &rval) {
                (RxType::IntLiteral, t, RxValue::IntLiteral(v), _) if t.is_concrete_int() => (
                    t.clone(),
                    Self::coerce_int_literal(*v, t),
                    rty.clone(),
                    rval,
                ),
                (t, RxType::IntLiteral, _, RxValue::IntLiteral(v)) if t.is_concrete_int() => (
                    lty.clone(),
                    lval,
                    t.clone(),
                    Self::coerce_int_literal(*v, t),
                ),
                _ => (lty, lval, rty, rval),
            }
        };
        let (lty, lval, rty, rval) = coerce_pair(lty, lval, rty, rval);

        // Arithmetic & bitwise for integer types
        if lty.is_integer() && rty.is_integer() {
            let result = match op_tok.token_type {
                Plus => Self::arith2(lty.clone(), lval.clone(), rval.clone(), |a, b| {
                    a.wrapping_add(b)
                }),
                Minus => Self::arith2(lty.clone(), lval.clone(), rval.clone(), |a, b| {
                    a.wrapping_sub(b)
                }),
                Mul => Self::arith2(lty.clone(), lval.clone(), rval.clone(), |a, b| {
                    a.wrapping_mul(b)
                }),
                Div => {
                    if Self::is_zero(&rval) {
                        return Err(SemanticError::InvalidConstExpr {
                            expr: "division by zero".to_string(),
                            line: report_tok.position.line,
                            column: report_tok.position.column,
                        });
                    }
                    Self::arith2(lty.clone(), lval.clone(), rval.clone(), |a, b| {
                        if b == 0 { 0 } else { a / b }
                    })
                }
                Percent => {
                    if Self::is_zero(&rval) {
                        return Err(SemanticError::InvalidConstExpr {
                            expr: "mod by zero".to_string(),
                            line: report_tok.position.line,
                            column: report_tok.position.column,
                        });
                    }
                    Self::arith2(lty.clone(), lval.clone(), rval.clone(), |a, b| {
                        if b == 0 { 0 } else { a % b }
                    })
                }
                And => Self::arith2(lty.clone(), lval.clone(), rval.clone(), |a, b| a & b),
                Or => Self::arith2(lty.clone(), lval.clone(), rval.clone(), |a, b| a | b),
                Xor => Self::arith2(lty.clone(), lval.clone(), rval.clone(), |a, b| a ^ b),
                SL => Self::arith2(lty.clone(), lval.clone(), rval.clone(), |a, b| a << b),
                SR => Self::arith2(lty.clone(), lval.clone(), rval.clone(), |a, b| a >> b),
                EqEq | NEq | Lt | LEq | Gt | GEq => {
                    let (lv, rv) = Self::as_i128_pair(&lval, &rval);
                    let res = match op_tok.token_type {
                        EqEq => lv == rv,
                        NEq => lv != rv,
                        Lt => lv < rv,
                        LEq => lv <= rv,
                        Gt => lv > rv,
                        GEq => lv >= rv,
                        _ => unreachable!(),
                    };
                    return Ok((RxType::Bool, RxValue::Bool(res)));
                }
                _ => {
                    /* fall through */
                    return Err(SemanticError::Generic {
                        msg: format!("unsupported binary op {:?} for integers", op_tok.token_type),
                        line: report_tok.position.line,
                        column: report_tok.position.column,
                    });
                }
            }?; // arithmetic path returns same type as lty
            return Ok(result);
        }

        // Logical
        match (lty.clone(), rty.clone(), op_tok.token_type) {
            (RxType::Bool, RxType::Bool, AndAnd) => {
                if let (RxValue::Bool(lb), RxValue::Bool(rb)) = (lval, rval) {
                    return Ok((RxType::Bool, RxValue::Bool(lb && rb)));
                }
            }
            (RxType::Bool, RxType::Bool, OrOr) => {
                if let (RxValue::Bool(lb), RxValue::Bool(rb)) = (lval, rval) {
                    return Ok((RxType::Bool, RxValue::Bool(lb || rb)));
                }
            }
            (lt, rt, AndAnd | OrOr) => {
                return Err(SemanticError::InvalidLogicalTypes {
                    left: lt,
                    right: rt,
                    line: report_tok.position.line,
                    column: report_tok.position.column,
                });
            }
            _ => {}
        }

        Err(SemanticError::InvalidConstExpr {
            expr: format!("unsupported operands for {:?}", op_tok.token_type),
            line: report_tok.position.line,
            column: report_tok.position.column,
        })
    }

    fn arith2(
        ty: RxType,
        lval: RxValue,
        rval: RxValue,
        f: impl Fn(i128, i128) -> i128,
    ) -> SemanticResult<(RxType, RxValue)> {
        let (lv, rv) = Self::as_i128_pair(&lval, &rval);
        let res = f(lv, rv);
        Ok((ty.clone(), Self::from_i128(res, &ty)))
    }

    fn is_zero(v: &RxValue) -> bool {
        matches!(
            v,
            RxValue::I32(0)
                | RxValue::U32(0)
                | RxValue::ISize(0)
                | RxValue::USize(0)
                | RxValue::IntLiteral(0)
        )
    }

    fn as_i128_pair(a: &RxValue, b: &RxValue) -> (i128, i128) {
        (Self::as_i128(a), Self::as_i128(b))
    }

    fn as_i128(v: &RxValue) -> i128 {
        match v {
            RxValue::I32(x) => *x as i128,
            RxValue::U32(x) => *x as i128,
            RxValue::ISize(x) => *x as i128,
            RxValue::USize(x) => *x as i128,
            RxValue::IntLiteral(x) => *x as i128,
            _ => 0,
        }
    }

    fn from_i128(v: i128, ty: &RxType) -> RxValue {
        match ty {
            RxType::I32 => RxValue::I32(v as i32),
            RxType::U32 => RxValue::U32(v as u32),
            RxType::ISize => RxValue::ISize(v as isize),
            RxType::USize => RxValue::USize(v as usize),
            RxType::IntLiteral => RxValue::IntLiteral(v as i64),
            _ => RxValue::IntLiteral(v as i64),
        }
    }

    fn coerce_int_literal(v: i64, target: &RxType) -> RxValue {
        match target {
            RxType::I32 => RxValue::I32(v as i32),
            RxType::U32 => RxValue::U32(v as u32),
            RxType::ISize => RxValue::ISize(v as isize),
            RxType::USize => RxValue::USize(v as usize),
            RxType::IntLiteral => RxValue::IntLiteral(v),
            _ => RxValue::IntLiteral(v),
        }
    }

    fn type_from_node(t: &TypeNode, report_tok: &Token) -> SemanticResult<RxType> {
        Ok(match t {
            TypeNode::I32(_) => RxType::I32,
            TypeNode::U32(_) => RxType::U32,
            TypeNode::ISize(_) => RxType::ISize,
            TypeNode::USize(_) => RxType::USize,
            TypeNode::Bool(_) => RxType::Bool,
            TypeNode::String(_) => RxType::String,
            TypeNode::Str(_) => RxType::Str,
            TypeNode::Char(_) => RxType::Char,
            TypeNode::Unit => RxType::Unit,
            _ => {
                return Err(SemanticError::InvalidConstExpr {
                    expr: format!("unsupported type annotation for const: {t:?}"),
                    line: report_tok.position.line,
                    column: report_tok.position.column,
                });
            }
        })
    }
}
