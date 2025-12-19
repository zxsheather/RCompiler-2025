use crate::{
    frontend::{
        r_lexer::token::TokenType,
        r_parser::ast::{ArrayLiteralNode, ExpressionNode, FunctionNode, ParamNode, TypeNode},
        r_semantic::{
            analyzer::SelfKind,
            const_folder::ConstFolder,
            tyctxt::{NodeId, TypeContext},
            types::{RxType, RxValue},
        },
    },
    middleend::ir::{
        error::{LowerError, LowerResult},
        module::{IRBinaryOp, IRCastOp, IRICmpOp, IRType, IRValue},
    },
};

pub fn convert_type_node(type_ctx: &TypeContext, node: &TypeNode) -> Option<IRType> {
    match node {
        TypeNode::I32(_) | TypeNode::U32(_) | TypeNode::ISize(_) | TypeNode::USize(_) => {
            Some(IRType::I32)
        }
        TypeNode::Bool(_) => Some(IRType::I8),
        TypeNode::Char(_) => Some(IRType::I8),
        TypeNode::Str(_) => Some(ir_type_for_str()),
        TypeNode::String(_) => Some(ir_type_for_string()),
        TypeNode::Unit => Some(IRType::Void),
        TypeNode::Array { elem_type, size } => ir_type_for_array(type_ctx, elem_type, size),
        TypeNode::Named(name) => {
            let struct_name = name.lexeme.clone();
            if let Some(layout) = type_ctx.get_struct_layout(&struct_name) {
                let fields = layout
                    .fields
                    .iter()
                    .map(|field| rx_to_ir_type(type_ctx, &field.ty))
                    .collect();
                Some(IRType::Struct { fields })
            } else {
                Some(IRType::Void) // Unknown struct, this should not happen
            }
        }
        TypeNode::Ref { inner_type, .. } => {
            let inner = convert_type_node(type_ctx, inner_type)?;
            Some(IRType::Ptr(Box::new(inner)))
        }
        TypeNode::Tuple(_) => Some(IRType::Void), // TO BE DONE: handle tuple type. Currently tuples are removed.
        TypeNode::SelfRef { .. } => None,         // Self type should be resolved before lowering
    }
}

pub fn rx_to_ir_type(type_ctx: &TypeContext, rx_type: &RxType) -> IRType {
    match rx_type {
        RxType::I32 | RxType::U32 | RxType::ISize | RxType::USize | RxType::IntLiteral => {
            IRType::I32
        }
        RxType::Bool => IRType::I8,
        RxType::Char => IRType::I8,
        RxType::MainReturn => IRType::I32,
        RxType::Str => ir_type_for_str(),
        RxType::String => ir_type_for_string(),
        RxType::Unit | RxType::Never => IRType::Void,
        RxType::Ref(inner, _) => {
            let inner_ir = rx_to_ir_type(type_ctx, inner);
            IRType::Ptr(Box::new(inner_ir))
        }
        RxType::Array(elem_type, None) => {
            let mut elem_ir = rx_to_ir_type(type_ctx, elem_type);
            if matches!(elem_ir, IRType::Void) {
                elem_ir = IRType::I8; // use i8 for void element type
            }
            IRType::Ptr(Box::new(elem_ir))
        }
        RxType::Array(elem_type, Some(size)) => {
            let mut elem_ir = rx_to_ir_type(type_ctx, elem_type);
            if matches!(elem_ir, IRType::Void) {
                elem_ir = IRType::I8;
            }
            IRType::Array {
                elem_type: Box::new(elem_ir),
                size: *size,
            }
        }
        RxType::Tuple(_) => IRType::Void, // TO BE DONE: handle tuple type. Currently tuples are removed.
        RxType::Struct(name) => {
            if let Some(layout) = type_ctx.get_struct_layout(name) {
                let fields = layout
                    .fields
                    .iter()
                    .map(|field| rx_to_ir_type(type_ctx, &field.ty))
                    .collect();
                IRType::Struct { fields }
            } else {
                IRType::Void // Unknown struct, this should not happen
            }
        }
    }
}

pub fn ir_const_from_rx(
    type_ctx: &TypeContext,
    ty: &RxType,
    value: &RxValue,
) -> LowerResult<IRValue> {
    let ir_ty = rx_to_ir_type(type_ctx, ty);
    let int_value = match ty {
        RxType::Bool => match value {
            RxValue::Bool(b) => Ok(if *b { 1 } else { 0 }),
            other => Err(LowerError::UnsupportedExpression(format!(
                "unsupported const value {other:?} of type {ty:?}"
            ))),
        },
        RxType::Char => match value {
            RxValue::Char(c) => Ok(*c as i64),
            other => Err(LowerError::UnsupportedExpression(format!(
                "unsupported const value {other:?} of type {ty:?}"
            ))),
        },
        RxType::I32 | RxType::IntLiteral | RxType::MainReturn | RxType::ISize => match value {
            RxValue::I32(v) => Ok(*v as i64),
            RxValue::U32(v) => Ok(*v as i64),
            RxValue::ISize(v) => Ok(*v as i64),
            RxValue::USize(v) => Ok(*v as i64),
            RxValue::IntLiteral(v) => Ok(*v),
            other => Err(LowerError::UnsupportedExpression(format!(
                "unsupported const value {other:?} of type {ty:?}"
            ))),
        },
        RxType::USize | RxType::U32 => match value {
            RxValue::USize(v) => Ok(*v as i64),
            RxValue::U32(v) => Ok(*v as i64),
            RxValue::IntLiteral(_) => match value {
                RxValue::IntLiteral(v) if *v >= 0 => Ok(*v),
                other => Err(LowerError::UnsupportedExpression(format!(
                    "unsupported const value {other:?} of type {ty:?}"
                ))),
            },
            other => Err(LowerError::UnsupportedExpression(format!(
                "unsupported const value {other:?} of type {ty:?}"
            ))),
        },
        other_ty => Err(LowerError::UnsupportedExpression(format!(
            "unsupported const type {other_ty:?}"
        ))),
    }?;
    Ok(IRValue::ConstInt {
        value: int_value,
        ty: ir_ty,
    })
}

pub fn ir_type_for_string() -> IRType {
    IRType::Struct {
        fields: vec![ir_type_for_str(), IRType::I32],
    }
}

pub fn ir_type_for_str() -> IRType {
    IRType::Struct {
        fields: vec![IRType::Ptr(Box::new(IRType::I8)), IRType::I32],
    }
}

pub fn ir_type_for_array(
    type_ctx: &TypeContext,
    elem_type: &TypeNode,
    size: &Option<Box<ExpressionNode>>,
) -> Option<IRType> {
    let mut elem = convert_type_node(type_ctx, elem_type)?;
    if matches!(elem, IRType::Void) {
        elem = IRType::I8; // use i8 for void element type
    }
    if let Some(len_expr) = size {
        if let Some(len) = array_length_from_expr(type_ctx, len_expr) {
            return Some(IRType::Array {
                elem_type: Box::new(elem),
                size: len,
            });
        }
    }
    // Use ptr for unsized array
    Some(IRType::Ptr(Box::new(elem)))
}

pub fn ir_type_hint_from_rx(type_ctx: &TypeContext, rx_type: &RxType) -> Option<IRType> {
    let ir_ty = rx_to_ir_type(type_ctx, rx_type);
    if matches!(ir_ty, IRType::Void) {
        None
    } else {
        Some(ir_ty)
    }
}

pub fn array_length_from_expr(type_ctx: &TypeContext, expr: &ExpressionNode) -> Option<usize> {
    // TO BE DONE: handle more cases like const variables
    match expr {
        ExpressionNode::IntegerLiteral(token, _) => {
            let (_, value) = ConstFolder::parse_int_literal(token).ok()?;
            rx_val_to_usize(&value)
        }
        ExpressionNode::Identifier(token, _) => type_ctx
            .get_const_value(&token.lexeme)
            .and_then(|(_, value)| rx_val_to_usize(value)),
        _ => None,
    }
}

pub fn rx_val_to_usize(value: &RxValue) -> Option<usize> {
    match value {
        RxValue::IntLiteral(v) => usize::try_from(*v).ok(),
        RxValue::I32(v) => usize::try_from(*v).ok(),
        RxValue::U32(v) => Some(*v as usize),
        RxValue::ISize(v) => usize::try_from(*v).ok(),
        RxValue::USize(v) => Some(*v),
        _ => None,
    }
}

pub fn int_bit_width(ty: &IRType) -> Option<usize> {
    match ty {
        IRType::I1 => Some(1),
        IRType::I8 => Some(8),
        IRType::I32 => Some(32),
        _ => None,
    }
}

pub fn expression_node_id(expr: &ExpressionNode) -> Option<NodeId> {
    match expr {
        ExpressionNode::Identifier(_, id)
        | ExpressionNode::IntegerLiteral(_, id)
        | ExpressionNode::StringLiteral(_, id)
        | ExpressionNode::BoolLiteral(_, id)
        | ExpressionNode::CharLiteral(_, id)
        | ExpressionNode::Underscore(_, id) => Some(*id),
        ExpressionNode::Unary(node) => Some(node.node_id),
        ExpressionNode::Binary(node) => Some(node.node_id),
        ExpressionNode::Call(node) => Some(node.node_id),
        ExpressionNode::MethodCall(node) => Some(node.node_id),
        ExpressionNode::Index(node) => Some(node.node_id),
        ExpressionNode::If(node) => Some(node.node_id),
        ExpressionNode::While(node) => Some(node.node_id),
        ExpressionNode::Loop(node) => Some(node.node_id),
        ExpressionNode::Member(node) => Some(node.node_id),
        ExpressionNode::Ref(node) => Some(node.node_id),
        ExpressionNode::Deref(node) => Some(node.node_id),
        ExpressionNode::Return(node) => Some(node.node_id),
        ExpressionNode::Break(node) => Some(node.node_id),
        ExpressionNode::Continue(node) => Some(node.node_id),
        ExpressionNode::As(node) => Some(node.node_id),
        ExpressionNode::Block(block) => Some(block.node_id),
        ExpressionNode::TupleLiteral(node) => Some(node.node_id),
        ExpressionNode::ArrayLiteral(node) => match node {
            ArrayLiteralNode::Elements { node_id, .. }
            | ArrayLiteralNode::Repeated { node_id, .. } => Some(*node_id),
        },
        ExpressionNode::StructLiteral(node) => Some(node.node_id),
        ExpressionNode::StaticMember(node) => Some(node.node_id),
    }
}

pub fn func_sig_hints(type_ctx: &TypeContext, name: &str) -> (Option<Vec<IRType>>, Option<IRType>) {
    if let Some(sig) = type_ctx.get_function(name) {
        let params = sig
            .params()
            .iter()
            .map(|ty| rx_to_ir_type(type_ctx, ty))
            .collect();
        let return_type = rx_to_ir_type(type_ctx, sig.return_type());
        (Some(params), Some(return_type))
    } else {
        (None, None)
    }
}

pub fn derive_param_ir_type(type_ctx: &TypeContext, param: &ParamNode) -> LowerResult<IRType> {
    type_ctx
        .get_type(param.node_id)
        .cloned()
        .map(|rx| rx_to_ir_type(type_ctx, &rx))
        .or_else(|| {
            param
                .type_annotation
                .as_ref()
                .and_then(|node| convert_type_node(type_ctx, node))
        })
        .ok_or_else(|| LowerError::MissingParameterType(param.name.lexeme.clone())) // This should not happen
}

pub fn determine_return_type(
    type_ctx: &TypeContext,
    func: &FunctionNode,
    return_hint: Option<IRType>,
) -> IRType {
    if let Some(hint) = return_hint {
        return hint;
    }
    if let Some(node) = &func.return_type {
        if let Some(ir) = convert_type_node(type_ctx, node) {
            return ir;
        }
    }
    IRType::Void
}

pub fn mangle_symbol_name(raw: &str) -> String {
    if raw.is_empty() {
        return "_".to_string();
    }

    let mut result = String::with_capacity(raw.len() + 1);
    for (idx, ch) in raw.chars().enumerate() {
        let mapped = match ch {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '_' | '.' => ch,
            _ => '_',
        };
        if idx == 0 && !matches!(mapped, 'a'..='z' | 'A'..='Z' | '_') {
            result.push('_');
        }
        result.push(mapped);
    }

    result
}

pub fn map_compound_binary_op(token: &TokenType) -> Option<IRBinaryOp> {
    match token {
        TokenType::PlusEq => Some(IRBinaryOp::Add),
        TokenType::MinusEq => Some(IRBinaryOp::Sub),
        TokenType::MulEq => Some(IRBinaryOp::Mul),
        TokenType::DivEq => Some(IRBinaryOp::SDiv),
        TokenType::ModEq => Some(IRBinaryOp::SRem),
        TokenType::AndEq => Some(IRBinaryOp::And),
        TokenType::OrEq => Some(IRBinaryOp::Or),
        TokenType::XorEq => Some(IRBinaryOp::Xor),
        TokenType::SLEq => Some(IRBinaryOp::Shl),
        TokenType::SREq => Some(IRBinaryOp::AShr),
        _ => None,
    }
}

pub fn map_compare_op(token: &TokenType) -> Option<IRICmpOp> {
    match token {
        TokenType::EqEq => Some(IRICmpOp::Eq),
        TokenType::NEq => Some(IRICmpOp::Ne),
        TokenType::Lt => Some(IRICmpOp::Slt),
        TokenType::LEq => Some(IRICmpOp::Sle),
        TokenType::Gt => Some(IRICmpOp::Sgt),
        TokenType::GEq => Some(IRICmpOp::Sge),
        _ => None,
    }
}

pub fn map_binary_op(token: &TokenType) -> Option<IRBinaryOp> {
    match token {
        TokenType::Plus => Some(IRBinaryOp::Add),
        TokenType::Minus => Some(IRBinaryOp::Sub),
        TokenType::Mul => Some(IRBinaryOp::Mul),
        TokenType::Div => Some(IRBinaryOp::SDiv),
        TokenType::Percent => Some(IRBinaryOp::SRem),
        TokenType::And => Some(IRBinaryOp::And),
        TokenType::Or => Some(IRBinaryOp::Or),
        TokenType::Xor => Some(IRBinaryOp::Xor),
        TokenType::SL => Some(IRBinaryOp::Shl),
        TokenType::SR => Some(IRBinaryOp::AShr),
        _ => None,
    }
}

pub fn determine_cast_op(from: &IRType, to: &IRType) -> LowerResult<Option<IRCastOp>> {
    if from == to {
        return Ok(None);
    }

    match (from, to) {
        (IRType::Ptr(_), IRType::Ptr(_)) => Ok(Some(IRCastOp::BitCast)),
        (IRType::Ptr(_), IRType::I32) => Ok(Some(IRCastOp::PtrToInt)),
        (IRType::I32, IRType::Ptr(_)) => Ok(Some(IRCastOp::IntToPtr)),
        _ => {
            if let (Some(from_bits), Some(to_bits)) = (int_bit_width(from), int_bit_width(to)) {
                if from_bits > to_bits {
                    Ok(Some(IRCastOp::Trunc))
                } else if from_bits < to_bits {
                    Ok(Some(IRCastOp::ZExt))
                } else {
                    Ok(None) // Should not reach here
                }
            } else {
                Err(LowerError::UnsupportedCast(format!(
                    "cannot cast from {from:?} to {to:?}"
                )))
            }
        }
    }
}

pub fn const_i32(value: i64) -> IRValue {
    IRValue::ConstInt {
        value,
        ty: IRType::I32,
    }
}

pub fn is_unsigned_integer_type(ty: &RxType) -> bool {
    matches!(ty, RxType::U32 | RxType::USize)
}

pub fn array_length_from_type(ty: &RxType) -> Option<usize> {
    match ty {
        RxType::Array(_, Some(size)) => Some(*size),
        RxType::Ref(inner, _) => array_length_from_type(inner),
        _ => None,
    }
}

pub fn resolve_method_self_type(self_kind: &SelfKind, obj_ty: &RxType) -> RxType {
    fn strip_ref(rx: &RxType) -> RxType {
        match rx {
            RxType::Ref(inner, _) => strip_ref(inner),
            other => other.clone(),
        }
    }

    match self_kind {
        SelfKind::Owned { ty } => ty.clone(),
        SelfKind::Borrowed { ty } => RxType::Ref(Box::new(ty.clone()), false),
        SelfKind::BorrowedMut { ty } => RxType::Ref(Box::new(ty.clone()), true),
        SelfKind::TraitOwned => strip_ref(obj_ty),
        SelfKind::TraitBorrowed => RxType::Ref(Box::new(strip_ref(obj_ty)), false),
        SelfKind::TraitBorrowedMut => RxType::Ref(Box::new(strip_ref(obj_ty)), true),
        SelfKind::None => obj_ty.clone(),
    }
}
