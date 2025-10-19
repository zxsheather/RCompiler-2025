use std::collections::{HashMap, HashSet};

use crate::{
    frontend::{
        r_lexer::token::{self, TokenType},
        r_parser::ast::{
            ArrayLiteralNode, AssignStatementNode, AstNode, BlockNode, ElseBodyNode,
            ExpressionNode, FunctionNode, IfExprNode, LetStatementNode, StatementNode,
            StructLiteralNode,
        },
        r_semantic::{
            analyzer::SelfKind,
            tyctxt::{self, NodeId, TypeContext},
            types::RxType,
        },
    },
    middleend::ir::{
        error::{LowerError, LowerResult},
        module::{
            IRBasicBlock, IRFunction, IRInstruction, IRInstructionKind, IRNode, IRType, IRValue,
        },
        utils::{
            const_i32, convert_type_node, derive_param_ir_type, determine_return_type,
            expression_node_id, func_sig_hints, mangle_symbol_name, rx_to_ir_type,
        },
    },
};

const ENTRY_BLOCK_LABEL: &str = "entry";

pub struct Lower<'a> {
    nodes: &'a [AstNode],
    type_ctx: &'a TypeContext,
}

impl<'a> Lower<'a> {
    pub fn new(nodes: &'a [AstNode], type_ctx: &'a TypeContext) -> Self {
        Self { nodes, type_ctx }
    }

    pub fn lower_program(&self, module_name: &str) -> LowerResult<()> {
        // Implement the lowering logic here
        let mut funcs = Vec::new();
        let mut defined_symbols = HashSet::new();
        for node in self.nodes {
            match node {
                AstNode::Function(func) => {
                    let (param_hints, return_hint) =
                        func_sig_hints(self.type_ctx, &func.name.lexeme);
                    let ir_name = func.name.lexeme.clone();
                    self.lower_function_with_nested(
                        func,
                        ir_name,
                        param_hints,
                        return_hint,
                        &mut funcs,
                        &mut defined_symbols,
                    )?;
                }
                AstNode::Statement(stmt) => {
                    self.lower_nested_functions_in_statement(
                        stmt,
                        &mut funcs,
                        &mut defined_symbols,
                    )?;
                }
                AstNode::Impl(impl_block) => {
                    let type_name = impl_block.name.lexeme.clone();
                    for method in &impl_block.methods {
                        let raw = format!("{}::{}", type_name, method.name.lexeme);
                        let ir_name = mangle_symbol_name(&raw);
                        let sig = self.type_ctx.get_method(&type_name, &method.name.lexeme);
                        let (param_hints, return_hint) = if let Some(sig) = sig {
                            let self_ty = match &sig.self_kind {
                                SelfKind::Owned { ty }
                                | SelfKind::Borrowed { ty }
                                | SelfKind::BorrowedMut { ty } => ty.clone(),
                                SelfKind::TraitOwned
                                | SelfKind::TraitBorrowed
                                | SelfKind::TraitBorrowedMut
                                | SelfKind::None => RxType::Struct(type_name.clone()),
                            };

                            let self_rx = match &sig.self_kind {
                                SelfKind::Borrowed { .. } => {
                                    RxType::Ref(Box::new(self_ty.clone()), false)
                                }
                                SelfKind::BorrowedMut { .. } => {
                                    RxType::Ref(Box::new(self_ty.clone()), true)
                                }
                                _ => self_ty,
                            };

                            let mut params = vec![rx_to_ir_type(self.type_ctx, &self_rx)];
                            params.extend(
                                sig.params()
                                    .iter()
                                    .map(|rx| rx_to_ir_type(self.type_ctx, rx)),
                            );
                            let return_type = rx_to_ir_type(self.type_ctx, sig.return_type());
                            (Some(params), Some(return_type))
                        } else {
                            (None, None)
                        };
                        self.lower_function_with_nested(
                            method,
                            ir_name,
                            param_hints,
                            return_hint,
                            &mut funcs,
                            &mut defined_symbols,
                        )?;
                    }
                }
                AstNode::ImplTrait(trait_impl) => {
                    let type_name = trait_impl.type_name.lexeme.clone();
                    for method in &trait_impl.methods {
                        let raw = format!("{}::{}", type_name, method.name.lexeme);
                        let ir_name = mangle_symbol_name(&raw);
                        let sig = self.type_ctx.get_method(&type_name, &method.name.lexeme);
                        let (param_hints, return_hint) = if let Some(sig) = sig {
                            let mut params = Vec::with_capacity(1 + sig.params().len());
                            let base_ty = match &sig.self_kind {
                                SelfKind::Owned { ty }
                                | SelfKind::Borrowed { ty }
                                | SelfKind::BorrowedMut { ty } => ty.clone(),
                                SelfKind::TraitOwned
                                | SelfKind::TraitBorrowed
                                | SelfKind::TraitBorrowedMut
                                | SelfKind::None => RxType::Struct(type_name.clone()),
                            };
                            let self_rx = match &sig.self_kind {
                                SelfKind::Borrowed { .. } | SelfKind::TraitBorrowed { .. } => {
                                    RxType::Ref(Box::new(base_ty.clone()), false)
                                }
                                SelfKind::BorrowedMut { .. }
                                | SelfKind::TraitBorrowedMut { .. } => {
                                    RxType::Ref(Box::new(base_ty.clone()), true)
                                }
                                _ => base_ty,
                            };
                            params.push(rx_to_ir_type(self.type_ctx, &self_rx));
                            params.extend(
                                sig.params()
                                    .iter()
                                    .map(|rx| rx_to_ir_type(self.type_ctx, rx)),
                            );
                            let ret = rx_to_ir_type(self.type_ctx, sig.return_type());
                            (Some(params), Some(ret))
                        } else {
                            (None, None)
                        };
                        self.lower_function_with_nested(
                            method,
                            ir_name,
                            param_hints,
                            return_hint,
                            &mut funcs,
                            &mut defined_symbols,
                        )?;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub fn lower_function_with_nested(
        &self,
        func: &FunctionNode,
        ir_name: String,
        param_hints: Option<Vec<IRType>>,
        return_hint: Option<IRType>,
        funcs: &mut Vec<IRFunction>,
        defined_symbols: &mut HashSet<String>,
    ) -> LowerResult<()> {
        let inserted = defined_symbols.insert(ir_name.clone());
        if inserted {
            let ir_func = self.lower_function_def(func, ir_name, param_hints, return_hint)?;
            funcs.push(ir_func);
        }
        self.lower_nested_functions_in_block(&func.body, funcs, defined_symbols)?;
        Ok(())
    }

    pub fn lower_nested_functions_in_block(
        &self,
        block: &BlockNode,
        funcs: &mut Vec<IRFunction>,
        defined_symbols: &mut HashSet<String>,
    ) -> LowerResult<()> {
        for stmt in &block.stats {
            self.lower_nested_functions_in_statement(stmt, funcs, defined_symbols)?;
        }
        if let Some(expr) = &block.final_expr {
            self.lower_nested_functions_in_expression(expr, funcs, defined_symbols)?;
        }
        Ok(())
    }

    pub fn lower_nested_functions_in_statement(
        &self,
        stmt: &StatementNode,
        funcs: &mut Vec<IRFunction>,
        defined_symbols: &mut HashSet<String>,
    ) -> LowerResult<()> {
        match stmt {
            StatementNode::Func(func) => {
                let (param_hints, return_hint) = func_sig_hints(self.type_ctx, &func.name.lexeme);
                let ir_name = func.name.lexeme.clone();
                self.lower_function_with_nested(
                    func,
                    ir_name,
                    param_hints,
                    return_hint,
                    funcs,
                    defined_symbols,
                )?;
            }
            StatementNode::Block(block) => {
                self.lower_nested_functions_in_block(block, funcs, defined_symbols)?;
            }
            StatementNode::Let(node) => {
                if let Some(expr) = &node.value {
                    self.lower_nested_functions_in_expression(expr, funcs, defined_symbols)?;
                }
            }
            StatementNode::Assign(node) => {
                self.lower_nested_functions_in_expression(&node.value, funcs, defined_symbols)?;
            }
            StatementNode::Expression(expr_stmt) => {
                self.lower_nested_functions_in_expression(
                    &expr_stmt.expression,
                    funcs,
                    defined_symbols,
                )?;
            }
            StatementNode::Const(node) => {
                self.lower_nested_functions_in_expression(&node.value, funcs, defined_symbols)?;
            }
            StatementNode::Struct(_) => {}
        }
        Ok(())
    }

    pub fn lower_nested_functions_in_expression(
        &self,
        expr: &ExpressionNode,
        funcs: &mut Vec<IRFunction>,
        defined_symbols: &mut HashSet<String>,
    ) -> LowerResult<()> {
        match expr {
            ExpressionNode::Block(block) => {
                self.lower_nested_functions_in_block(block, funcs, defined_symbols)?;
            }
            ExpressionNode::If(if_expr) => {
                self.lower_nested_function_in_if_expr(if_expr, funcs, defined_symbols)?;
            }
            ExpressionNode::While(while_expr) => {
                self.lower_nested_functions_in_expression(
                    &while_expr.condition,
                    funcs,
                    defined_symbols,
                )?;
                self.lower_nested_functions_in_block(&while_expr.body, funcs, defined_symbols)?;
            }
            ExpressionNode::Loop(loop_expr) => {
                self.lower_nested_functions_in_block(&loop_expr.body, funcs, defined_symbols)?;
            }
            ExpressionNode::Unary(node) => {
                self.lower_nested_functions_in_expression(&node.operand, funcs, defined_symbols)?;
            }
            ExpressionNode::Binary(node) => {
                self.lower_nested_functions_in_expression(
                    &node.left_operand,
                    funcs,
                    defined_symbols,
                )?;
                self.lower_nested_functions_in_expression(
                    &node.right_operand,
                    funcs,
                    defined_symbols,
                )?;
            }
            ExpressionNode::Call(call) => {
                self.lower_nested_functions_in_expression(&call.function, funcs, defined_symbols)?;
                for arg in &call.args {
                    self.lower_nested_functions_in_expression(arg, funcs, defined_symbols)?;
                }
            }
            ExpressionNode::MethodCall(call) => {
                self.lower_nested_functions_in_expression(&call.object, funcs, defined_symbols)?;
                for arg in &call.args {
                    self.lower_nested_functions_in_expression(arg, funcs, defined_symbols)?;
                }
            }
            ExpressionNode::Index(index) => {
                self.lower_nested_functions_in_expression(&index.array, funcs, defined_symbols)?;
                self.lower_nested_functions_in_expression(&index.index, funcs, defined_symbols)?;
            }
            ExpressionNode::StructLiteral(node) => {
                for field in &node.fields {
                    self.lower_nested_functions_in_expression(
                        &field.value,
                        funcs,
                        defined_symbols,
                    )?;
                }
            }
            ExpressionNode::TupleLiteral(node) => {
                for elem in &node.elements {
                    self.lower_nested_functions_in_expression(elem, funcs, defined_symbols)?;
                }
            }
            ExpressionNode::ArrayLiteral(array) => match array {
                ArrayLiteralNode::Elements { elements, .. } => {
                    for elem in elements {
                        self.lower_nested_functions_in_expression(elem, funcs, defined_symbols)?;
                    }
                }
                ArrayLiteralNode::Repeated { element, size, .. } => {
                    self.lower_nested_functions_in_expression(element, funcs, defined_symbols)?;
                    self.lower_nested_functions_in_expression(size, funcs, defined_symbols)?;
                }
            },
            ExpressionNode::Member(member) => {
                self.lower_nested_functions_in_expression(&member.object, funcs, defined_symbols)?;
            }
            ExpressionNode::Ref(node) => {
                self.lower_nested_functions_in_expression(&node.operand, funcs, defined_symbols)?;
            }
            ExpressionNode::Deref(node) => {
                self.lower_nested_functions_in_expression(&node.operand, funcs, defined_symbols)?;
            }
            ExpressionNode::Return(ret) => {
                if let Some(expr) = &ret.value {
                    self.lower_nested_functions_in_expression(expr, funcs, defined_symbols)?;
                }
            }
            ExpressionNode::As(as_expr) => {
                self.lower_nested_functions_in_expression(&as_expr.expr, funcs, defined_symbols)?;
            }
            ExpressionNode::Break(brk) => {
                if let Some(expr) = &brk.value {
                    self.lower_nested_functions_in_expression(expr, funcs, defined_symbols)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    pub fn lower_nested_function_in_if_expr(
        &self,
        if_expr: &IfExprNode,
        funcs: &mut Vec<IRFunction>,
        defined_symbols: &mut HashSet<String>,
    ) -> LowerResult<()> {
        self.lower_nested_functions_in_expression(&if_expr.condition, funcs, defined_symbols)?;
        self.lower_nested_functions_in_block(&if_expr.then_block, funcs, defined_symbols)?;
        if let Some(else_body) = &if_expr.else_block {
            match else_body {
                ElseBodyNode::Block(block) => {
                    self.lower_nested_functions_in_block(block.as_ref(), funcs, defined_symbols)?;
                }
                ElseBodyNode::If(nested_if) => {
                    self.lower_nested_function_in_if_expr(nested_if, funcs, defined_symbols)?;
                }
            }
        }
        Ok(())
    }

    pub fn lower_function_def(
        &self,
        func: &FunctionNode,
        ir_name: String,
        param_hints: Option<Vec<IRType>>,
        return_hint: Option<IRType>,
    ) -> LowerResult<IRFunction> {
        let mut builder =
            FunctionBuilder::new(func, self.type_ctx, ir_name, param_hints, return_hint)?;
        builder.lower_function_body()?;
        builder.finish()
    }
}

pub struct FunctionBuilder<'a> {
    func: &'a FunctionNode,
    type_ctx: &'a TypeContext,
    params: Vec<(String, IRType)>,
    return_type: IRType,
    blocks: Vec<IRBasicBlock>,
    current_block: IRBasicBlock,
    temp_counter: usize,
    scopes: Vec<HashMap<String, Binding>>,
    ir_name: String,
    loop_stack: Vec<LoopFrame>,
    param_mutability: HashMap<String, bool>,
    entry_allocas: Vec<IRInstruction>,
}

impl<'a> FunctionBuilder<'a> {
    pub fn new(
        func: &'a FunctionNode,
        type_ctx: &'a TypeContext,
        ir_name: String,
        param_hints: Option<Vec<IRType>>,
        return_hint: Option<IRType>,
    ) -> LowerResult<Self> {
        let mut params = Vec::new();
        let mut param_mutability = HashMap::new();
        let mut hints_iter = param_hints.map(|vec| vec.into_iter());

        for param in &func.param_list.params {
            let ty = if let Some(iter) = hints_iter.as_mut() {
                if let Some(hint_ty) = iter.next() {
                    hint_ty
                } else {
                    derive_param_ir_type(type_ctx, param)?
                }
            } else {
                derive_param_ir_type(type_ctx, param)?
            };
            param_mutability.insert(param.name.lexeme.clone(), param.mutable);
            params.push((param.name.lexeme.clone(), ty));
        }
        let return_type = determine_return_type(type_ctx, func, return_hint);

        Ok(Self {
            func,
            type_ctx,
            params,
            return_type,
            blocks: Vec::new(),
            current_block: IRBasicBlock {
                label: ENTRY_BLOCK_LABEL.to_string(),
                instructions: Vec::new(),
                terminator: None,
            },
            temp_counter: 0,
            scopes: Vec::new(),
            ir_name,
            loop_stack: Vec::new(),
            param_mutability,
            entry_allocas: Vec::new(),
        })
    }

    pub fn lower_function_body(&mut self) -> LowerResult<()> {
        self.push_scope();
        let params = self.params.clone();
        for (idx, (name, ty)) in params.iter().enumerate() {
            let arg = IRValue::Argument {
                index: idx,
                name: Some(name.clone()),
                ty: ty.clone(),
            };

            let requires_stack_slot = self.param_mutability.get(name).cloned().unwrap_or(false)
                || matches!(ty, IRType::Array { .. } | IRType::Struct { .. });
            if requires_stack_slot {
                let ptr_ty = IRType::Ptr(Box::new(ty.clone()));
                let alloca = self.emit_value_instr(
                    IRInstructionKind::Alloca {
                        alloc_type: ty.clone(),
                        align: None,
                    },
                    ptr_ty.clone(),
                );
                self.emit_store(arg.clone(), alloca.clone())?;
                self.bind_value(name.clone(), Binding::Pointer(alloca));
            } else {
                self.bind_value(name.clone(), Binding::Value(arg));
            }
        }
        Ok(())
    }

    pub fn finish(mut self) -> LowerResult<IRFunction> {
        self.blocks.push(self.current_block);
        if let Some(entry_block) = self.blocks.first_mut() {
            if !self.entry_allocas.is_empty() {
                let mut combined_instructions =
                    Vec::with_capacity(self.entry_allocas.len() + entry_block.instructions.len());
                combined_instructions.extend(self.entry_allocas);
                combined_instructions.extend(entry_block.instructions.drain(..));
                entry_block.instructions = combined_instructions;
            }
        }
        Ok(IRFunction {
            name: self.ir_name,
            params: self.params,
            return_type: self.return_type,
            basic_blocks: self.blocks,
        })
    }

    pub fn lower_block(&mut self, block: &BlockNode) -> LowerResult<Option<IRValue>> {
        self.push_scope();
        let mut idx = 0;
        while idx < block.stats.len() {
            // Check for early termination
            if self.has_terminated() {
                break;
            }

            // Look ahead for consecutive let statements with the same identifier
            if let StatementNode::Let(first) = &block.stats[idx] {
                let mut last = idx;
                let mut look_ahead = idx + 1;
                while look_ahead < block.stats.len() {
                    match &block.stats[look_ahead] {
                        StatementNode::Let(next)
                            if next.identifier.lexeme == first.identifier.lexeme
                                && !next
                                    .value
                                    .as_ref()
                                    .map(|v| {
                                        Self::expr_uses_identifier(v, &first.identifier.lexeme)
                                    })
                                    .unwrap_or(false) =>
                        {
                            last = look_ahead;
                            look_ahead += 1;
                        }
                        _ => break,
                    }
                }
                if last != idx {
                    idx = last;
                }
            }

            self.lower_statement(&block.stats[idx])?;
            idx += 1;
        }
        let value = if !self.has_terminated() {
            if let Some(final_expr) = &block.final_expr {
                Some(self.lower_expression(final_expr)?)
            } else {
                None
            }
        } else {
            None
        };
        self.pop_scope();
        Ok(value)
    }

    pub fn lower_statement(&mut self, stmt: &StatementNode) -> LowerResult<()> {
        Ok(())
    }

    pub fn lower_let(&mut self, node: LetStatementNode) -> LowerResult<()> {
        if matches!(node.identifier.token_type, TokenType::Underscore) {
            if let Some(expr) = &node.value {
                let _ = self.lower_expression(expr)?;
            }
            return Ok(());
        }

        let var_name = node.identifier.lexeme.clone();
        let expr_type = if let Some(expr) = &node.value {
            match self.expression_value_type(expr) {
                Ok(opt) => opt,
                Err(LowerError::MissingType(_)) => None,
                Err(e) => return Err(e),
            }
        } else {
            None
        };
        let annotated_type = if let Some(type_node) = &node.type_annotation {
            convert_type_node(self.type_ctx, type_node)
        } else {
            None
        };
        let ctx_type = self
            .type_ctx
            .get_type(node.node_id)
            .map(|ty| rx_to_ir_type(self.type_ctx, &ty));
        let value_type = if let Some(expr_ty) = expr_type {
            expr_ty
        } else if let Some(annot_ty) = annotated_type {
            annot_ty
        } else if let Some(ctx_ty) = ctx_type {
            ctx_ty
        } else {
            return Err(LowerError::MissingBindingType(var_name.clone()));
        };

        let ptr_ty = IRType::Ptr(Box::new(value_type.clone()));
        let alloca = self.emit_value_instr(
            IRInstructionKind::Alloca {
                alloc_type: value_type.clone(),
                align: None,
            },
            ptr_ty.clone(),
        );
        if let Some(expr) = &node.value {
            if !self.store_literal_into_pointer(&alloca, expr)? {
                let init_val = self.lower_expression(expr)?;
                self.emit_store(init_val, alloca.clone())?;
            }
        }

        self.bind_value(var_name, Binding::Pointer(alloca));
        Ok(())
    }

    pub fn lower_assign(&mut self, node: &AssignStatementNode) -> LowerResult<()> {
        Ok(())
    }

    pub fn lower_expression(&mut self, expr: &ExpressionNode) -> LowerResult<IRValue> {
        Ok(IRValue::ConstNull(IRType::I32))
    }

    pub fn store_literal_into_pointer(
        &mut self,
        dest_ptr: &IRValue,
        expr: &ExpressionNode,
    ) -> LowerResult<bool> {
        match expr {
            ExpressionNode::StructLiteral(literal) => {
                self.store_struct_literal(dest_ptr, literal)?;
                Ok(true)
            }
            ExpressionNode::ArrayLiteral(literal) => {
                self.store_array_literal(dest_ptr, literal)?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    pub fn store_struct_literal(
        &mut self,
        dest_ptr: &IRValue,
        literal: &StructLiteralNode,
    ) -> LowerResult<()> {
        let layout = self
            .type_ctx
            .get_struct_layout(&literal.name.lexeme)
            .ok_or_else(|| {
                LowerError::UnsupportedExpression(format!(
                    "unknown struct type: {}",
                    &literal.name.lexeme
                ))
            })?;

        for field in &literal.fields {
            let field_name = field.name.lexeme.as_str();
            let (index, field_layout) = layout
                .fields
                .iter()
                .enumerate()
                .find(|(_, f)| f.name == field_name)
                .ok_or_else(|| {
                    LowerError::UnsupportedExpression(format!(
                        "struct {} has no field named {}",
                        &literal.name.lexeme, field_name
                    ))
                })?;
            let field_ty = rx_to_ir_type(self.type_ctx, &field_layout.ty);
            let field_ptr = self.emit_value_instr(
                IRInstructionKind::GetElementPtr {
                    base: dest_ptr.clone(),
                    indices: vec![const_i32(0), const_i32(index as i64)],
                    in_bounds: true,
                },
                IRType::Ptr(Box::new(field_ty.clone())),
            );
            if self.store_literal_into_pointer(&field_ptr, &field.value)? {
                continue;
            }
            let value = self.lower_expression(&field.value)?;
            self.emit_store(value, field_ptr)?;
        }
        Ok(())
    }

    pub fn store_array_literal(
        &mut self,
        dest_ptr: &IRValue,
        literal: &ArrayLiteralNode,
    ) -> LowerResult<()> {
        let (node_id, length_hint) = match literal {
            ArrayLiteralNode::Elements { node_id, elements } => (*node_id, Some(elements.len())),
            ArrayLiteralNode::Repeated { node_id, .. } => (*node_id, None),
        };
        let layout = self
            .type_ctx
            .get_array_layout(node_id)
            .ok_or_else(|| LowerError::UnsupportedExpression("unknown array type".to_string()))?;
        let elem_ty = rx_to_ir_type(self.type_ctx, &layout.elem_type);
        let length = length_hint.or(layout.size).ok_or_else(|| {
            LowerError::UnsupportedExpression(format!(
                "array literal missing length information: {:?}",
                literal
            ))
        })?;
        match literal {
            ArrayLiteralNode::Elements { elements, .. } => {
                for (index, expr) in elements.iter().enumerate() {
                    let elem_ptr = self.emit_value_instr(
                        IRInstructionKind::GetElementPtr {
                            base: dest_ptr.clone(),
                            indices: vec![const_i32(0), const_i32(index as i64)],
                            in_bounds: true,
                        },
                        IRType::Ptr(Box::new(elem_ty.clone())),
                    );
                    if self.store_literal_into_pointer(&elem_ptr, expr)? {
                        continue;
                    }
                    let value = self.lower_expression(expr)?;
                    self.emit_store(value, elem_ptr)?;
                }
            }
            ArrayLiteralNode::Repeated { element, .. } => {
                let mut cached_value: Option<IRValue> = None;
                for index in 0..length {
                    let elem_ptr = self.emit_value_instr(
                        IRInstructionKind::GetElementPtr {
                            base: dest_ptr.clone(),
                            indices: vec![const_i32(0), const_i32(index as i64)],
                            in_bounds: true,
                        },
                        IRType::Ptr(Box::new(elem_ty.clone())),
                    );
                    if self.store_literal_into_pointer(&elem_ptr, element)? {
                        continue;
                    }
                    let value = if let Some(cached) = &cached_value {
                        cached.clone()
                    } else {
                        let val = self.lower_expression(element)?;
                        cached_value = Some(val.clone());
                        val
                    };
                    self.emit_store(value, elem_ptr)?;
                }
            }
        }
        Ok(())
    }

    fn expr_uses_identifier(expr: &ExpressionNode, name: &str) -> bool {
        match expr {
            ExpressionNode::Identifier(token, _) => token.lexeme == name,
            ExpressionNode::Block(block) => Self::block_uses_identifier(block, name),
            ExpressionNode::TupleLiteral(tuple) => tuple
                .elements
                .iter()
                .any(|elem| Self::expr_uses_identifier(elem, name)),
            ExpressionNode::ArrayLiteral(array) => match array {
                ArrayLiteralNode::Elements { elements, .. } => elements
                    .iter()
                    .any(|elem| Self::expr_uses_identifier(elem, name)),
                ArrayLiteralNode::Repeated { element, size, .. } => {
                    Self::expr_uses_identifier(element, name)
                        || Self::expr_uses_identifier(size, name)
                }
            },
            ExpressionNode::StructLiteral(struct_lit) => struct_lit
                .fields
                .iter()
                .any(|field| Self::expr_uses_identifier(&field.value, name)),
            ExpressionNode::StaticMember(_) => false,
            ExpressionNode::Binary(node) => {
                Self::expr_uses_identifier(&node.left_operand, name)
                    || Self::expr_uses_identifier(&node.right_operand, name)
            }
            ExpressionNode::Unary(node) => Self::expr_uses_identifier(&node.operand, name),
            ExpressionNode::Call(node) => {
                Self::expr_uses_identifier(&node.function, name)
                    || node
                        .args
                        .iter()
                        .any(|arg| Self::expr_uses_identifier(arg, name))
            }
            ExpressionNode::MethodCall(node) => {
                Self::expr_uses_identifier(&node.object, name)
                    || node
                        .args
                        .iter()
                        .any(|arg| Self::expr_uses_identifier(arg, name))
            }
            ExpressionNode::Index(node) => {
                Self::expr_uses_identifier(&node.array, name)
                    || Self::expr_uses_identifier(&node.index, name)
            }
            ExpressionNode::If(node) => Self::if_expr_uses_identifier(node, name),
            ExpressionNode::While(node) => {
                Self::expr_uses_identifier(&node.condition, name)
                    || Self::block_uses_identifier(&node.body, name)
            }
            ExpressionNode::Loop(node) => Self::block_uses_identifier(&node.body, name),
            ExpressionNode::Ref(node) => Self::expr_uses_identifier(&node.operand, name),
            ExpressionNode::Deref(node) => Self::expr_uses_identifier(&node.operand, name),
            ExpressionNode::Return(node) => node
                .value
                .as_ref()
                .map_or(false, |expr| Self::expr_uses_identifier(expr, name)),
            ExpressionNode::As(node) => Self::expr_uses_identifier(&node.expr, name),
            ExpressionNode::Break(node) => node
                .value
                .as_ref()
                .map_or(false, |expr| Self::expr_uses_identifier(expr, name)),
            _ => false,
        }
    }

    pub fn block_uses_identifier(block: &BlockNode, name: &str) -> bool {
        true
    }

    pub fn if_expr_uses_identifier(if_expr: &IfExprNode, name: &str) -> bool {
        if Self::expr_uses_identifier(&if_expr.condition, name) {
            return true;
        }
        if Self::block_uses_identifier(&if_expr.then_block, name) {
            return true;
        }
        if let Some(else_body) = &if_expr.else_block {
            match else_body {
                ElseBodyNode::Block(block) => {
                    if Self::block_uses_identifier(block, name) {
                        return true;
                    }
                }
                ElseBodyNode::If(nested_if) => {
                    if Self::if_expr_uses_identifier(nested_if, name) {
                        return true;
                    }
                }
            }
        }
        false
    }

    pub fn emit_value_instr(&mut self, kind: IRInstructionKind, ty: IRType) -> IRValue {
        let name = format!("t{}", self.temp_counter);
        self.temp_counter += 1;
        let value = IRValue::InstructionRef {
            id: name,
            ty: ty.clone(),
        };
        let is_alloca = matches!(kind, IRInstructionKind::Alloca { .. });
        let instr = IRInstruction::new(kind).with_result(value.clone(), Some(ty));
        if is_alloca {
            self.entry_allocas.push(instr);
        } else {
            self.current_block.instructions.push(instr);
        }
        value
    }
    pub fn emit_void_instr(&mut self, kind: IRInstructionKind) {
        let instr = IRInstruction::new(kind);
        self.current_block.instructions.push(instr);
    }
    pub fn emit_store(&mut self, value: IRValue, ptr: IRValue) -> LowerResult<()> {
        if !matches!(ptr.get_type(), IRType::Ptr(_)) {
            return Err(LowerError::UnsupportedExpression(format!(
                "cannot store void value into {:?}",
                ptr.get_type()
            )));
        }
        if matches!(value.get_type(), IRType::Void) {
            return Err(LowerError::UnsupportedExpression(
                "cannot store void value".to_string(),
            ));
        }
        self.emit_void_instr(IRInstructionKind::Store {
            value,
            ptr,
            align: None,
        });
        Ok(())
    }
    pub fn bind_value(&mut self, name: String, binding: Binding) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name, binding);
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn has_terminated(&self) -> bool {
        self.current_block.terminator.is_some()
    }

    fn expression_value_type(&self, expr: &ExpressionNode) -> LowerResult<Option<IRType>> {
        if let Some(node_id) = expression_node_id(expr) {
            self.node_value_type(node_id)
        } else {
            Ok(None)
        }
    }

    fn node_value_type(&self, node_id: NodeId) -> LowerResult<Option<IRType>> {
        let Some(rx_type) = self.type_ctx.get_type(node_id) else {
            return Err(LowerError::MissingType(node_id));
        };
        let ir_type = rx_to_ir_type(self.type_ctx, &rx_type);
        if matches!(ir_type, IRType::Void) {
            Ok(None)
        } else {
            Ok(Some(ir_type))
        }
    }
}

#[derive(Debug, Clone)]
pub enum Binding {
    Value(IRValue),
    Pointer(IRValue),
}

#[derive(Debug, Clone)]
pub struct LoopFrame {
    break_label: String,
    continue_label: String,
    result_ty: Option<IRType>,
    break_value: Vec<(IRValue, String)>,
}

impl LoopFrame {
    pub fn new(break_label: String, continue_label: String, result_ty: Option<IRType>) -> Self {
        Self {
            break_label,
            continue_label,
            result_ty,
            break_value: Vec::new(),
        }
    }
}
