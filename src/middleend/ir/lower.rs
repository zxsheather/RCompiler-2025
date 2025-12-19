use std::collections::{HashMap, HashSet};

use crate::{
    frontend::{
        r_lexer::token::{self, TokenType},
        r_parser::ast::{
            ArrayLiteralNode, AsExprNode, AssignStatementNode, AstNode, BinaryExprNode, BlockNode,
            BreakExprNode, CallExprNode, ConstItemNode, ContinueExprNode, DerefExprNode,
            ElseBodyNode, ExpressionNode, FunctionNode, IfExprNode, IndexExprNode,
            LetStatementNode, LoopExprNode, MemberExprNode, MethodCallExprNode, RefExprNode,
            ReturnExprNode, StatementNode, StructLiteralNode, UnaryExprNode, WhileExprNode,
        },
        r_semantic::{
            analyzer::SelfKind,
            built_in::{get_built_in_funcs, get_built_in_methods, get_built_in_static_methods},
            tyctxt::{NodeId, TypeContext},
            types::RxType,
        },
    },
    middleend::ir::{
        builtins::build_builtin_lowering,
        error::{LowerError, LowerResult},
        module::{
            CallTarget, IRBasicBlock, IRBinaryOp, IRCastOp, IRFunction, IRICmpOp, IRInstruction,
            IRInstructionKind, IRModule, IRType, IRValue,
        },
        utils::{
            array_length_from_type, const_i32, convert_type_node, derive_param_ir_type,
            determine_cast_op, determine_return_type, expression_node_id, func_sig_hints,
            ir_const_from_rx, ir_type_hint_from_rx, is_unsigned_integer_type, mangle_symbol_name,
            map_binary_op, map_compare_op, map_compound_binary_op, resolve_method_self_type,
            rx_to_ir_type,
        },
    },
};

pub const ENTRY_BLOCK_LABEL: &str = "fn_entry";

fn should_use_sret(ty: &IRType) -> bool {
    matches!(ty, IRType::Struct { .. })
}

pub struct Lower<'a> {
    nodes: &'a [AstNode],
    type_ctx: &'a TypeContext,
}

impl<'a> Lower<'a> {
    pub fn new(nodes: &'a [AstNode], type_ctx: &'a TypeContext) -> Self {
        Self { nodes, type_ctx }
    }

    pub fn lower_program(&self, module_name: &str) -> LowerResult<IRModule> {
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

        self.append_builtin_declarations(&mut funcs, &defined_symbols);
        Ok(IRModule {
            name: module_name.to_string(),
            funcs,
        })
    }

    pub fn append_builtin_declarations(
        &self,
        funcs: &mut Vec<IRFunction>,
        defined_symbols: &HashSet<String>,
    ) {
        let builtin_lowering = build_builtin_lowering(self.type_ctx, defined_symbols);
        let mut synthesized = HashSet::new();

        for extern_func in builtin_lowering.externs {
            synthesized.insert(extern_func.name.clone());
            if funcs.iter().any(|f| f.name == extern_func.name) {
                continue;
            }
            funcs.push(extern_func);
        }

        for builtin in builtin_lowering.functions {
            synthesized.insert(builtin.name.clone());
            if defined_symbols.contains(&builtin.name) {
                continue;
            }
            funcs.push(builtin);
        }

        for (name, _) in get_built_in_funcs() {
            let ir_name = mangle_symbol_name(name);
            if synthesized.contains(&ir_name) || defined_symbols.contains(&ir_name) {
                continue;
            }
            if let Some(sig) = self.type_ctx.get_function(name) {
                let params = sig
                    .params()
                    .iter()
                    .enumerate()
                    .map(|(idx, rx)| (format!("arg{idx}"), rx_to_ir_type(self.type_ctx, rx)))
                    .collect();
                let return_type = rx_to_ir_type(self.type_ctx, sig.return_type());
                let ir_func = IRFunction {
                    name: ir_name,
                    params,
                    return_type,
                    basic_blocks: Vec::new(),
                };
                funcs.push(ir_func);
            }
        }

        for (type_name, method_name, _) in get_built_in_methods() {
            let raw_name = format!("{}::{}", type_name, method_name);
            let ir_name = mangle_symbol_name(&raw_name);
            if defined_symbols.contains(&ir_name) || synthesized.contains(&ir_name) {
                continue;
            }
            if let Some(sig) = self.type_ctx.get_method(type_name, method_name) {
                let mut params = Vec::with_capacity(1 + sig.params().len());
                let base_ty = match &sig.self_kind {
                    SelfKind::Owned { ty }
                    | SelfKind::Borrowed { ty }
                    | SelfKind::BorrowedMut { ty } => ty.clone(),
                    SelfKind::TraitOwned
                    | SelfKind::TraitBorrowed
                    | SelfKind::TraitBorrowedMut
                    | SelfKind::None => RxType::Struct(type_name.to_string()),
                };
                let self_rx = match &sig.self_kind {
                    SelfKind::Borrowed { .. } => RxType::Ref(Box::new(base_ty.clone()), false),
                    SelfKind::BorrowedMut { .. } => RxType::Ref(Box::new(base_ty.clone()), true),
                    _ => base_ty,
                };
                params.push(("self".to_string(), rx_to_ir_type(self.type_ctx, &self_rx)));
                for (idx, rx) in sig.params().iter().enumerate() {
                    params.push((format!("arg{}", idx), rx_to_ir_type(self.type_ctx, rx)));
                }

                let return_type = rx_to_ir_type(self.type_ctx, sig.return_type());
                funcs.push(IRFunction {
                    name: ir_name,
                    params,
                    return_type,
                    basic_blocks: Vec::new(),
                });
            }
        }

        for (type_name, method_name, _) in get_built_in_static_methods() {
            let raw_name = format!("{}::{}", type_name, method_name);
            let ir_name = mangle_symbol_name(&raw_name);
            if defined_symbols.contains(&ir_name) || synthesized.contains(&ir_name) {
                continue;
            }
            if let Some(sig) = self.type_ctx.get_method(type_name, method_name) {
                let params = sig
                    .params()
                    .iter()
                    .enumerate()
                    .map(|(idx, rx)| (format!("arg{idx}"), rx_to_ir_type(self.type_ctx, rx)))
                    .collect();
                let return_type = rx_to_ir_type(self.type_ctx, sig.return_type());
                funcs.push(IRFunction {
                    name: ir_name,
                    params,
                    return_type,
                    basic_blocks: Vec::new(),
                });
            }
        }
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
    sret_ptr: Option<IRValue>,
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
        let mut return_type = determine_return_type(type_ctx, func, return_hint);

        if should_use_sret(&return_type) {
            let sret_arg_name = "__sret_ptr".to_string();
            let sret_ty = IRType::Ptr(Box::new(return_type.clone()));
            params.insert(0, (sret_arg_name.clone(), sret_ty.clone()));
            return_type = IRType::Void;
        }

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
            sret_ptr: None,
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

            if name == "__sret_ptr" {
                self.sret_ptr = Some(arg.clone());
                self.bind_value(name.clone(), Binding::Value(arg));
                continue;
            }

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

        let result = self.lower_block(&self.func.body)?;

        if !self.has_terminated() {
            if let Some(sret) = &self.sret_ptr {
                if let Some(value) = result {
                    // We need to store the result into the sret pointer
                    // The value might need coercion if it's not exactly the same type (unlikely if type checked)
                    // But `coerce_to_return_type` uses `self.return_type` which is now Void.
                    // We should use the original return type for coercion if we had it.
                    // But `value` should already be the correct type from `lower_block`.
                    self.emit_store(value, sret.clone())?;
                    self.emit_return(None);
                } else {
                    // If result is None but we have sret, it means we are missing a return value
                    return Err(LowerError::MissingReturnValue(
                        self.func.name.lexeme.clone(),
                    ));
                }
            } else {
                match (&self.return_type, result) {
                    (IRType::Void, _) => self.emit_return(None),
                    (_, Some(value)) => {
                        let coerced = self.coerce_to_return_type(value)?;
                        self.emit_return(Some(coerced));
                    }
                    (IRType::I32, None) if self.func.name.lexeme == "main" => {
                        let zero = const_i32(0);
                        self.emit_return(Some(zero));
                    }
                    (_, None) => {
                        return Err(LowerError::MissingReturnValue(
                            self.func.name.lexeme.clone(),
                        ));
                    }
                }
            }
        }
        self.pop_scope();
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
        match stmt {
            StatementNode::Let(node) => self.lower_let(node.clone()),
            StatementNode::Assign(node) => self.lower_assign(node),
            StatementNode::Expression(expr_stmt) => {
                self.lower_expression(&expr_stmt.expression)?;
                Ok(())
            }
            StatementNode::Block(block) => {
                self.lower_block(block)?;
                Ok(())
            }
            StatementNode::Const(node) => self.lower_const(node),
            StatementNode::Func(_) | StatementNode::Struct(_) => Ok(()),
        }
    }

    pub fn lower_const(&mut self, node: &ConstItemNode) -> LowerResult<()> {
        if let Some((rx_ty, rx_value)) = self.type_ctx.get_const_value(&node.name.lexeme) {
            let const_val = ir_const_from_rx(self.type_ctx, rx_ty, rx_value)?;
            self.bind_value(node.name.lexeme.clone(), Binding::Value(const_val));
            return Ok(());
        }

        let value = self.lower_expression(&node.value)?;
        self.bind_value(node.name.lexeme.clone(), Binding::Value(value));
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

        // Memcpy optimization: detect identifier-to-identifier assignment of large aggregates
        if let Some(expr) = &node.value {
            if let ExpressionNode::Identifier(src_token, _) = expr {
                if let Some(Binding::Pointer(src_ptr)) = self.lookup_binding(&src_token.lexeme) {
                    if matches!(value_type, IRType::Struct { .. } | IRType::Array { .. }) {
                        let size = Self::calculate_type_size(&value_type);
                        if size >= 16 {
                            // Use memcpy for large aggregates
                            self.emit_memcpy(alloca.clone(), src_ptr, &value_type)?;
                            self.bind_value(var_name, Binding::Pointer(alloca));
                            return Ok(());
                        }
                    }
                }
            }
        }

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
        let target = self
            .lookup_binding(&node.identifier.lexeme)
            .ok_or_else(|| LowerError::UndefinedIdentifier(node.identifier.lexeme.clone()))?;
        let Binding::Pointer(dest_ptr) = target else {
            return Err(LowerError::ImmutableBinding(node.identifier.lexeme.clone()));
        };

        // Memcpy optimization: detect identifier-to-identifier assignment of large aggregates
        if let ExpressionNode::Identifier(src_token, _) = &node.value {
            if let Some(Binding::Pointer(src_ptr)) = self.lookup_binding(&src_token.lexeme) {
                // Get the type of the destination
                if let IRType::Ptr(inner_ty) = dest_ptr.get_type() {
                    if matches!(
                        inner_ty.as_ref(),
                        IRType::Struct { .. } | IRType::Array { .. }
                    ) {
                        let size = Self::calculate_type_size(&inner_ty);
                        if size >= 16 {
                            // Use memcpy for large aggregates
                            self.emit_memcpy(dest_ptr.clone(), src_ptr, &inner_ty)?;
                            return Ok(());
                        }
                    }
                }
            }
        }

        if !self.store_literal_into_pointer(&dest_ptr, &node.value)? {
            let value = self.lower_expression(&node.value)?;
            self.emit_store(value, dest_ptr.clone())?;
        }
        Ok(())
    }

    pub fn lower_expression(&mut self, expr: &ExpressionNode) -> LowerResult<IRValue> {
        if self.has_terminated() {
            return Ok(IRValue::Undef(IRType::Void));
        }

        match expr {
            ExpressionNode::IntegerLiteral(token, node_id) => {
                self.lower_int_literal(token, *node_id)
            }
            ExpressionNode::BoolLiteral(token, node_id) => self.lower_bool_literal(token, *node_id),
            ExpressionNode::Identifier(token, node_id) => self.lower_identifier(token, *node_id),
            ExpressionNode::Binary(node) => self.lower_binary(node),
            ExpressionNode::Unary(node) => self.lower_unary(node),
            ExpressionNode::Member(member) => self.lower_member_expr(member),
            ExpressionNode::Index(index) => self.lower_index_expr(index),
            ExpressionNode::StructLiteral(literal) => self.lower_struct_literal_expr(literal),
            ExpressionNode::ArrayLiteral(literal) => self.lower_array_literal_expr(literal),
            ExpressionNode::Deref(node) => self.lower_deref_expr(node),
            ExpressionNode::Ref(node) => self.lower_ref_expr(node),
            ExpressionNode::Call(call) => self.lower_call_expr(call),
            ExpressionNode::MethodCall(call) => self.lower_method_call_expr(call),
            ExpressionNode::Block(block) => {
                let value = self.lower_block(block)?;
                Ok(value.unwrap_or(IRValue::Undef(IRType::Void)))
            }
            ExpressionNode::If(node) => self.lower_if_expr(node),
            ExpressionNode::While(node) => self.lower_while_expr(node),
            ExpressionNode::Loop(node) => self.lower_loop_expr(node),
            ExpressionNode::Break(node) => self.lower_break_expr(node),
            ExpressionNode::Continue(node) => self.lower_continue_expr(node),
            ExpressionNode::Return(node) => {
                self.lower_return(node)?;
                // After return, the control flow is interrupted.
                // We return Undef because this value shouldn't be used.
                // But we need to return something that matches the expected type if we are in an expression context?
                // Actually `lower_return` emits a Ret instruction which is a terminator.
                // So subsequent instructions in this block are unreachable.
                Ok(IRValue::Undef(IRType::Void))
            }
            ExpressionNode::As(node) => self.lower_as_expr(node),
            _ => Err(LowerError::UnsupportedExpression(format!(
                "unsupported expression: {:?}",
                expr
            ))),
        }
    }

    pub fn lower_int_literal(
        &mut self,
        token: &token::Token,
        node_id: NodeId,
    ) -> LowerResult<IRValue> {
        let ty = match self.node_value_type(node_id) {
            Ok(Some(ty)) => ty,
            // Err(LowerError::MissingType(_)) | Ok(None) => IRType::I32,
            Ok(None) => {
                return Err(LowerError::UnsupportedExpression(format!(
                    "cannot infer type for integer literal: {}",
                    token.lexeme
                )));
            }
            Err(e) => return Err(e),
        };
        let mut lexeme = token.lexeme.replace('_', "");
        for suffix in ["isize", "usize", "i32", "u32"] {
            if lexeme.ends_with(suffix) {
                lexeme = lexeme.trim_end_matches(suffix).to_string();
                break;
            }
        }
        let (base, digits) = if lexeme.starts_with("0x") {
            (16, &lexeme[2..])
        } else if lexeme.starts_with("0b") {
            (2, &lexeme[2..])
        } else if lexeme.starts_with("0o") {
            (8, &lexeme[2..])
        } else {
            (10, &lexeme[..])
        };
        if digits.is_empty() {
            return Err(LowerError::IntegerLiteral(token.lexeme.clone()));
        }
        let value = i64::from_str_radix(digits, base)
            .map_err(|_| LowerError::IntegerLiteral(token.lexeme.clone()))?;
        Ok(IRValue::ConstInt { value, ty })
    }

    pub fn lower_bool_literal(
        &mut self,
        token: &token::Token,
        node_id: NodeId,
    ) -> LowerResult<IRValue> {
        let ty = match self.node_value_type(node_id) {
            Ok(Some(t)) => t,
            Ok(None) => {
                return Err(LowerError::UnsupportedExpression(format!(
                    "cannot infer type for boolean literal: {}",
                    token.lexeme
                )));
            }
            Err(e) => return Err(e),
        };
        let value = match token.token_type {
            TokenType::True => 1,
            TokenType::False => 0,
            _ => {
                return Err(LowerError::UnsupportedExpression(format!(
                    "invalid boolean literal: {}",
                    token.lexeme
                )));
            }
        };
        Ok(IRValue::ConstInt { value, ty })
    }

    pub fn lower_identifier(
        &mut self,
        token: &token::Token,
        node_id: NodeId,
    ) -> LowerResult<IRValue> {
        if let Some(binding) = self.lookup_binding(&token.lexeme) {
            return match binding {
                Binding::Value(val) => Ok(val),
                Binding::Pointer(ptr) => {
                    let result_ty = match self.node_value_type(node_id) {
                        Ok(Some(ty)) => ty,
                        Ok(None) => {
                            return Err(LowerError::MissingType(node_id));
                        }
                        Err(e) => return Err(e),
                    };
                    let load = self
                        .emit_value_instr(IRInstructionKind::Load { ptr, align: None }, result_ty);
                    Ok(load)
                }
            };
        }
        if let Some((rx_ty, rx_value)) = self.type_ctx.get_const_value(&token.lexeme) {
            return ir_const_from_rx(self.type_ctx, rx_ty, rx_value);
        }
        Err(LowerError::UndefinedIdentifier(token.lexeme.clone()))
    }

    pub fn lower_binary(&mut self, node: &BinaryExprNode) -> LowerResult<IRValue> {
        match node.operator.token_type {
            TokenType::Eq => {
                return self.lower_expr_assign(
                    node.node_id,
                    &node.left_operand,
                    &node.right_operand,
                );
            }
            TokenType::AndAnd | TokenType::OrOr => {
                let is_or = matches!(node.operator.token_type, TokenType::OrOr);
                return self.lower_short_circuit(
                    node.node_id,
                    &node.left_operand,
                    &node.right_operand,
                    is_or,
                );
            }
            _ => {}
        }
        if let Some(op) = map_compound_binary_op(&node.operator.token_type) {
            let op = self.adjust_binary_op(op, node.node_id);
            return self.lower_compound_assign(
                node.node_id,
                &node.left_operand,
                &node.right_operand,
                op,
            );
        }
        if let Some(op) = map_compare_op(&node.operator.token_type) {
            let lhs = self.lower_expression(&node.left_operand)?;
            let rhs = self.lower_expression(&node.right_operand)?;
            let result_ty = match self.node_value_type(node.node_id) {
                Ok(Some(ty)) => ty,
                Ok(None) => IRType::I8, // Default to I8 for bool results
                Err(e) => return Err(e),
            };
            let op = self.adjust_compare_op(op, &node.operator.token_type, &node.left_operand)?;

            // ICmp returns i1 in LLVM, we need to extend it to i8
            let cmp_i1 =
                self.emit_value_instr(IRInstructionKind::ICmp { op, lhs, rhs }, IRType::I1);

            // Zero-extend i1 to i8
            let cmp_i8 = self.emit_value_instr(
                IRInstructionKind::Cast {
                    op: IRCastOp::ZExt,
                    value: cmp_i1,
                    to_type: result_ty.clone(),
                },
                result_ty,
            );

            return Ok(cmp_i8);
        }
        let op = map_binary_op(&node.operator.token_type).ok_or_else(|| {
            LowerError::UnsupportedExpression(format!(
                "unsupported binary operator: {:?}",
                node.operator.token_type
            ))
        })?;
        let op = self.adjust_binary_op(op, node.node_id);
        let lhs = self.lower_expression(&node.left_operand)?;
        let rhs = self.lower_expression(&node.right_operand)?;
        let result_ty = match self.node_value_type(node.node_id) {
            Ok(Some(ty)) => ty,
            Ok(None) => {
                return Err(LowerError::MissingType(node.node_id));
            }
            Err(e) => return Err(e),
        };
        let value = self.emit_value_instr(IRInstructionKind::Binary { op, lhs, rhs }, result_ty);
        Ok(value)
    }

    pub fn lower_unary(&mut self, node: &UnaryExprNode) -> LowerResult<IRValue> {
        let operand = self.lower_expression(&node.operand)?;
        let result_ty = match self.node_value_type(node.node_id) {
            Ok(Some(ty)) => ty,
            Ok(None) => {
                return Err(LowerError::MissingType(node.node_id));
            }
            Err(e) => return Err(e),
        };
        match node.operator.token_type {
            TokenType::Minus => {
                if !result_ty.is_integer_type() {
                    return Err(LowerError::TypeMismatch {
                        expected: IRType::I32,
                        found: operand.get_type(),
                    });
                }
                let zero = IRValue::ConstInt {
                    value: 0,
                    ty: result_ty.clone(),
                };
                let value = self.emit_value_instr(
                    IRInstructionKind::Binary {
                        op: IRBinaryOp::Sub,
                        lhs: zero,
                        rhs: operand,
                    },
                    result_ty,
                );
                Ok(value)
            }
            TokenType::Not => match operand.get_type() {
                IRType::I8 => {
                    // For bool (stored as i8), XOR with 1
                    let one = IRValue::ConstInt {
                        value: 1,
                        ty: IRType::I8,
                    };
                    let value = self.emit_value_instr(
                        IRInstructionKind::Binary {
                            op: IRBinaryOp::Xor,
                            lhs: operand,
                            rhs: one,
                        },
                        IRType::I8,
                    );
                    Ok(value)
                }
                IRType::I32 => {
                    // For integers, bitwise NOT
                    let ty = operand.get_type();
                    let mask = IRValue::ConstInt {
                        value: -1,
                        ty: ty.clone(),
                    };
                    let value = self.emit_value_instr(
                        IRInstructionKind::Binary {
                            op: IRBinaryOp::Xor,
                            lhs: operand,
                            rhs: mask,
                        },
                        ty,
                    );
                    Ok(value)
                }
                other => Err(LowerError::UnsupportedExpression(format!(
                    "cannot apply 'not' operator to type {:?}",
                    other
                ))),
            },
            other => Err(LowerError::UnsupportedExpression(format!(
                "unsupported unary operator: {:?}",
                other
            ))),
        }
    }

    pub fn lower_member_expr(&mut self, member: &MemberExprNode) -> LowerResult<IRValue> {
        let field_ptr = self.lower_struct_field_ptr(member)?;
        let result_ty = match self.node_value_type(member.node_id) {
            Ok(Some(ty)) => ty,
            Ok(None) => {
                return Err(LowerError::UnsupportedExpression(
                    "cannot determine type of member expression".to_string(),
                ));
            }
            Err(e) => return Err(e),
        };
        let value = self.emit_value_instr(
            IRInstructionKind::Load {
                ptr: field_ptr,
                align: None,
            },
            result_ty,
        );
        Ok(value)
    }

    pub fn lower_index_expr(&mut self, index: &IndexExprNode) -> LowerResult<IRValue> {
        let elem_ptr = self.lower_array_index_ptr(index)?;
        let result_ty = match self.node_value_type(index.node_id) {
            Ok(Some(ty)) => ty,
            // Ok(None) => match elem_ptr.get_type() {
            //     IRType::Ptr(inner) => inner.as_ref().clone(),
            //     other => {
            //         return Err(LowerError::UnsupportedExpression(format!(
            //             "cannot load from non-pointer binding {:?}",
            //             other
            //         )));
            //     }
            // },
            Ok(None) => {
                return Err(LowerError::UnsupportedExpression(
                    "cannot determine type of indexed expression".to_string(),
                ));
            }
            Err(e) => return Err(e),
        };
        let value = self.emit_value_instr(
            IRInstructionKind::Load {
                ptr: elem_ptr,
                align: None,
            },
            result_ty,
        );
        Ok(value)
    }

    pub fn lower_expr_assign(
        &mut self,
        node_id: NodeId,
        left_operand: &ExpressionNode,
        right_operand: &ExpressionNode,
    ) -> LowerResult<IRValue> {
        let ptr = self.lower_lvalue_pointer(left_operand)?;

        if self.store_literal_into_pointer(&ptr, right_operand)? {
            let load_ty = match ptr.get_type() {
                IRType::Ptr(inner) => inner.as_ref().clone(),
                other => {
                    return Err(LowerError::UnsupportedExpression(format!(
                        "cannot load from non-pointer binding {:?}",
                        other
                    )));
                }
            };
            let value = self.emit_value_instr(
                IRInstructionKind::Load {
                    ptr: ptr.clone(),
                    align: None,
                },
                load_ty,
            );
            return Ok(value);
        }

        let value = self.lower_expression(right_operand)?;
        self.emit_store(value.clone(), ptr.clone())?;
        if let Some(res_ty) = self.node_value_type(node_id)? {
            if res_ty != value.get_type() {
                return Err(LowerError::TypeMismatch {
                    expected: res_ty,
                    found: value.get_type(),
                });
            }
        }
        Ok(value)
    }

    pub fn lower_struct_literal_expr(
        &mut self,
        literal: &StructLiteralNode,
    ) -> LowerResult<IRValue> {
        let res_ty = match self.node_value_type(literal.node_id) {
            Ok(Some(ty)) => ty,
            Ok(None) => {
                return Err(LowerError::UnsupportedExpression(
                    "cannot determine struct literal type".to_string(),
                ));
            }
            Err(e) => return Err(e),
        };
        // let layout = self
        //     .type_ctx
        //     .get_struct_layout(&literal.name.lexeme)
        //     .ok_or_else(|| {
        //         LowerError::UnsupportedExpression(format!(
        //             "unknown struct type: {}",
        //             &literal.name.lexeme
        //         ))
        //     })?;
        let dest_ptr = self.emit_value_instr(
            IRInstructionKind::Alloca {
                alloc_type: res_ty.clone(),
                align: None,
            },
            IRType::Ptr(Box::new(res_ty.clone())),
        );
        self.store_struct_literal(&dest_ptr, literal)?;
        let aggregate = self.emit_value_instr(
            IRInstructionKind::Load {
                ptr: dest_ptr,
                align: None,
            },
            res_ty.clone(),
        );
        // let mut aggregate = IRValue::Undef(res_ty.clone());
        // for field in &literal.fields {
        //     let field_name = field.name.lexeme.as_str();
        //     let (index, field_layout) = layout
        //         .fields
        //         .iter()
        //         .enumerate()
        //         .find(|(_, f)| f.name == field_name)
        //         .ok_or_else(|| {
        //             LowerError::UnsupportedExpression(format!(
        //                 "struct {} has no field named {}",
        //                 &literal.name.lexeme, field_name
        //             ))
        //         })?;

        //     let field_value = self.lower_expression(&field.value)?;
        //     let field_ty = rx_to_ir_type(self.type_ctx, &field_layout.ty);
        //     if field_value.get_type() != field_ty {
        //         return Err(LowerError::TypeMismatch {
        //             expected: field_ty,
        //             found: field_value.get_type(),
        //         });
        //     }
        //     aggregate = self.emit_value_instr(
        //         IRInstructionKind::InsertValue {
        //             aggregate,
        //             value: field_value,
        //             indices: vec![index],
        //         },
        //         res_ty.clone(),
        //     );
        // }
        Ok(aggregate)
    }

    // Helper function to check if an expression is a zero value
    fn is_zero_value(expr: &ExpressionNode) -> bool {
        match expr {
            ExpressionNode::IntegerLiteral(token, _) => token.lexeme == "0",
            ExpressionNode::BoolLiteral(token, _) => token.lexeme == "false",
            _ => false,
        }
    }

    fn calculate_type_size(ty: &IRType) -> usize {
        Self::type_layout(ty).0
    }

    fn type_layout(ty: &IRType) -> (usize, usize) {
        match ty {
            IRType::I1 | IRType::I8 => (1, 1),
            IRType::I32 => (4, 4),
            IRType::Ptr(_) => (8, 8),
            IRType::Array { elem_type, size } => {
                let (elem_size, elem_align) = Self::type_layout(elem_type);
                let stride = Self::align_to(elem_size, elem_align);
                (stride * size, elem_align)
            }
            IRType::Struct { fields } => {
                let mut offset = 0usize;
                let mut max_align = 1usize;
                for field in fields {
                    let (field_size, field_align) = Self::type_layout(field);
                    offset = Self::align_to(offset, field_align);
                    offset += field_size;
                    if field_align > max_align {
                        max_align = field_align;
                    }
                }
                let total_size = Self::align_to(offset, max_align);
                (total_size, max_align)
            }
            IRType::Void => (0, 1),
        }
    }

    fn align_to(value: usize, align: usize) -> usize {
        if align <= 1 {
            return value;
        }
        ((value + align - 1) / align) * align
    }

    fn lower_array_literal_expr(&mut self, literal: &ArrayLiteralNode) -> LowerResult<IRValue> {
        let node_id = match literal {
            ArrayLiteralNode::Elements { node_id, .. } => *node_id,
            ArrayLiteralNode::Repeated { node_id, .. } => *node_id,
        };
        let result_ty = match self.node_value_type(node_id) {
            Ok(Some(ty)) => ty,
            Ok(None) => {
                return Err(LowerError::UnsupportedExpression(
                    "cannot determine array literal type".to_string(),
                ));
            }
            Err(e) => return Err(e),
        };
        let (elem_ty, size) = match &result_ty {
            IRType::Array { elem_type, size } => (elem_type.as_ref().clone(), *size),
            other => {
                return Err(LowerError::UnsupportedExpression(format!(
                    "expected array type for array literal, found {:?}",
                    other
                )));
            }
        };

        match literal {
            ArrayLiteralNode::Elements { elements, .. } => {
                let mut aggregate = IRValue::Undef(result_ty.clone());
                for (index, expr) in elements.iter().enumerate() {
                    let value = self.lower_expression(expr)?;
                    if value.get_type() != elem_ty {
                        return Err(LowerError::TypeMismatch {
                            expected: elem_ty.clone(),
                            found: value.get_type(),
                        });
                    }
                    aggregate = self.emit_value_instr(
                        IRInstructionKind::InsertValue {
                            aggregate,
                            value,
                            indices: vec![index],
                        },
                        result_ty.clone(),
                    );
                }
                Ok(aggregate)
            }
            ArrayLiteralNode::Repeated { element, .. } => {
                // Check if we can use memset optimization
                // memset can only be used when:
                // 1. Element type is i8 or i32
                // 2. The value is a constant 0
                // 3. The array size is reasonably large (> 16 elements)
                let use_memset = size > 16 && matches!(elem_ty, IRType::I8 | IRType::I32);

                if use_memset {
                    if let ExpressionNode::IntegerLiteral(token, _) = element.as_ref() {
                        if token.lexeme == "0" {
                            // Use memset optimization
                            // Allocate the array on stack
                            let alloc = self.emit_value_instr(
                                IRInstructionKind::Alloca {
                                    alloc_type: result_ty.clone(),
                                    align: None,
                                },
                                IRType::Ptr(Box::new(result_ty.clone())),
                            );

                            // In newer LLVM versions, ptr types only need to emit ptr,
                            // so we can directly use the alloc pointer as i8*. If we need
                            // to cast, uncomment the following code.

                            // let i8_ptr = self.emit_value_instr(
                            //     IRInstructionKind::Cast {
                            //         op: IRCastOp::BitCast,
                            //         value: alloc.clone(),
                            //         to_type: IRType::Ptr(Box::new(IRType::I8)),
                            //     },
                            //     IRType::Ptr(Box::new(IRType::I8)),
                            // );

                            // Calculate total bytes
                            let elem_size = match elem_ty {
                                IRType::I8 => 1,
                                IRType::I32 => 4,
                                _ => unreachable!(),
                            };
                            let total_bytes = size * elem_size;

                            // Call llvm.memset.p0.i32(ptr, 0, size, false)
                            self.emit_void_instr(IRInstructionKind::Call {
                                callee: CallTarget::Direct("llvm.memset.p0.i32".to_string()),
                                args: vec![
                                    alloc.clone(),
                                    IRValue::ConstInt {
                                        value: 0,
                                        ty: IRType::I8,
                                    },
                                    IRValue::ConstInt {
                                        value: total_bytes as i64,
                                        ty: IRType::I32,
                                    },
                                    IRValue::ConstInt {
                                        value: 0,
                                        ty: IRType::I1,
                                    }, // is_volatile = false
                                ],
                            });

                            // Load the initialized array
                            let result = self.emit_value_instr(
                                IRInstructionKind::Load {
                                    ptr: alloc,
                                    align: None,
                                },
                                result_ty.clone(),
                            );

                            return Ok(result);
                        }
                    }
                }

                // Fall back to insertvalue for non-zero values or small arrays
                let mut aggregate = IRValue::Undef(result_ty.clone());
                let mut cached_value: Option<IRValue> = None;
                for index in 0..size {
                    let value = if let Some(cached) = &cached_value {
                        cached.clone()
                    } else {
                        let val = self.lower_expression(element)?;
                        cached_value = Some(val.clone());
                        val
                    };
                    if value.get_type() != elem_ty {
                        return Err(LowerError::TypeMismatch {
                            expected: elem_ty.clone(),
                            found: value.get_type(),
                        });
                    }
                    aggregate = self.emit_value_instr(
                        IRInstructionKind::InsertValue {
                            aggregate,
                            value,
                            indices: vec![index],
                        },
                        result_ty.clone(),
                    );
                }
                Ok(aggregate)
            }
        }
    }

    pub fn lower_deref_expr(&mut self, node: &DerefExprNode) -> LowerResult<IRValue> {
        let ptr = self.lower_expression(&node.operand)?;
        let result_ty = match self.node_value_type(node.node_id) {
            Ok(Some(ty)) => ty,
            Ok(None) => {
                return Err(LowerError::MissingType(node.node_id));
            }
            Err(e) => return Err(e),
        };
        let value = self.emit_value_instr(IRInstructionKind::Load { ptr, align: None }, result_ty);
        Ok(value)
    }

    pub fn lower_ref_expr(&mut self, node: &RefExprNode) -> LowerResult<IRValue> {
        let ptr = self.lower_lvalue_pointer(&node.operand)?;
        let Some(res_ty) = self.node_value_type(node.node_id)? else {
            return Err(LowerError::MissingType(node.node_id));
        };
        if ptr.get_type() != res_ty {
            let casted = self.emit_value_instr(
                IRInstructionKind::Cast {
                    op: IRCastOp::BitCast,
                    value: ptr.clone(),
                    to_type: res_ty.clone(),
                },
                res_ty,
            );
            Ok(casted)
        } else {
            Ok(ptr)
        }
    }

    pub fn lower_call_expr(&mut self, call: &CallExprNode) -> LowerResult<IRValue> {
        let (callee, expected_params, return_hint) = match call.function.as_ref() {
            ExpressionNode::Identifier(token, _) => {
                let raw_name = token.lexeme.clone();
                let sig = self.type_ctx.get_function(&raw_name);
                let expected = sig.map(|s| s.params().len());
                let return_hint =
                    sig.and_then(|s| ir_type_hint_from_rx(self.type_ctx, s.return_type()));
                let ir_name = mangle_symbol_name(&raw_name);
                (CallTarget::Direct(ir_name), expected, return_hint)
            }
            ExpressionNode::StaticMember(sm) => {
                let Some(meta) = self.type_ctx.get_static_method_ref(sm.node_id) else {
                    return Err(LowerError::UnsupportedExpression(format!(
                        "unsolved static method {:?}",
                        sm,
                    )));
                };
                let sig = self
                    .type_ctx
                    .get_static_method(&meta.type_name, &meta.method_name);
                let expected = sig.map(|s| s.params().len());
                let return_hint =
                    sig.and_then(|s| ir_type_hint_from_rx(self.type_ctx, s.return_type()));
                let raw_name = format!("{}::{}", meta.type_name, meta.method_name);
                let ir_name = mangle_symbol_name(&raw_name);
                (CallTarget::Direct(ir_name), expected, return_hint)
            }
            other => {
                return Err(LowerError::UnsupportedExpression(format!(
                    "unsupported callee expression: {:?}",
                    other
                )));
            }
        };
        if let Some(exp) = expected_params {
            if exp != call.args.len() {
                return Err(LowerError::UnsupportedExpression(format!(
                    "expected {} arguments but found {}",
                    exp,
                    call.args.len()
                )));
            }
        }
        let mut args = Vec::with_capacity(call.args.len());
        for arg in &call.args {
            args.push(self.lower_expression(arg)?);
        }
        let ret_ty = match self.node_value_type(call.node_id) {
            Ok(ty) => ty,
            Err(e) => return Err(e),
        };
        let call_ty = ret_ty.or(return_hint);

        if let Some(ty) = call_ty {
            if should_use_sret(&ty) {
                // SRET handling
                let alloca = self.emit_value_instr(
                    IRInstructionKind::Alloca {
                        alloc_type: ty.clone(),
                        align: None,
                    },
                    IRType::Ptr(Box::new(ty.clone())),
                );
                args.insert(0, alloca.clone());
                self.emit_void_instr(IRInstructionKind::Call { callee, args });

                let load = self.emit_value_instr(
                    IRInstructionKind::Load {
                        ptr: alloca,
                        align: None,
                    },
                    ty,
                );
                Ok(load)
            } else {
                let value = self.emit_value_instr(IRInstructionKind::Call { callee, args }, ty);
                Ok(value)
            }
        } else {
            self.emit_void_instr(IRInstructionKind::Call { callee, args });
            Ok(IRValue::Undef(IRType::Void))
        }
    }

    fn lower_method_call_expr(&mut self, call: &MethodCallExprNode) -> LowerResult<IRValue> {
        let object_id = expression_node_id(&call.object).ok_or_else(|| {
            LowerError::UnsupportedExpression("invalid method call expression".to_string())
        })?;
        let obj_rx = self
            .type_ctx
            .get_type(object_id)
            .cloned()
            .ok_or_else(|| LowerError::MissingType(object_id))?;
        let type_name = obj_rx.method_key();
        if type_name.is_empty() {
            return Err(LowerError::UnsupportedExpression(format!(
                "type {:?} has no methods",
                obj_rx
            )));
        }

        let method_name = call.method.lexeme.clone();
        let sig = self
            .type_ctx
            .get_method(&type_name, &method_name)
            .ok_or_else(|| {
                LowerError::UnsupportedExpression(format!(
                    "type {} has no method named {}",
                    type_name, method_name
                ))
            })?;

        if type_name == "Array" && method_name == "len" {
            if let Some(len) = array_length_from_type(&obj_rx).or_else(|| {
                self.type_ctx
                    .get_array_layout(object_id)
                    .and_then(|layout| layout.size)
            }) {
                let ret_ty = rx_to_ir_type(self.type_ctx, sig.return_type());
                return Ok(IRValue::ConstInt {
                    value: len as i64,
                    ty: ret_ty,
                });
            }
        }

        let expected_self_rx = resolve_method_self_type(&sig.self_kind, &obj_rx);
        let receiver = self.prepare_method_receiver(&call.object, &expected_self_rx)?;
        if call.args.len() != sig.params().len() {
            return Err(LowerError::UnsupportedExpression(format!(
                "expected {} arguments but found {}",
                sig.params().len() - 1,
                call.args.len()
            )));
        }

        let mut args = Vec::with_capacity(call.args.len() + 1);
        args.push(receiver);
        for (arg_expr, param_ty) in call.args.iter().zip(sig.params()) {
            let arg_val = self.lower_expression(arg_expr)?;
            let expected_ir = rx_to_ir_type(self.type_ctx, param_ty);
            if arg_val.get_type() != expected_ir {
                return Err(LowerError::TypeMismatch {
                    expected: expected_ir,
                    found: arg_val.get_type(),
                });
            }
            args.push(arg_val);
        }

        let callee_symbol = mangle_symbol_name(&format!("{}::{}", type_name, method_name));
        let callee = CallTarget::Direct(callee_symbol);
        let res_ty = match self.node_value_type(call.node_id) {
            Ok(Some(ty)) => Some(ty),
            Ok(None) | Err(LowerError::MissingType(_)) => None,
            Err(e) => return Err(e),
        };
        if let Some(ty) = res_ty {
            if should_use_sret(&ty) {
                // SRET handling for method calls
                let alloca = self.emit_value_instr(
                    IRInstructionKind::Alloca {
                        alloc_type: ty.clone(),
                        align: None,
                    },
                    IRType::Ptr(Box::new(ty.clone())),
                );
                args.insert(0, alloca.clone());
                self.emit_void_instr(IRInstructionKind::Call { callee, args });

                let load = self.emit_value_instr(
                    IRInstructionKind::Load {
                        ptr: alloca,
                        align: None,
                    },
                    ty,
                );
                Ok(load)
            } else {
                let value = self.emit_value_instr(IRInstructionKind::Call { callee, args }, ty);
                Ok(value)
            }
        } else {
            self.emit_void_instr(IRInstructionKind::Call { callee, args });
            Ok(IRValue::Undef(IRType::Void))
        }
    }

    pub fn lower_compound_assign(
        &mut self,
        node_id: NodeId,
        left_operand: &ExpressionNode,
        right_operand: &ExpressionNode,
        op: IRBinaryOp,
    ) -> LowerResult<IRValue> {
        let ptr = self.lower_lvalue_pointer(left_operand)?;
        let value_ty = match self.expression_value_type(left_operand) {
            Ok(Some(ty)) => ty,
            Ok(None) => {
                return Err(LowerError::MissingType(node_id));
            }
            Err(e) => return Err(e),
        };
        let current = self.emit_value_instr(
            IRInstructionKind::Load {
                ptr: ptr.clone(),
                align: None,
            },
            value_ty.clone(),
        );
        let rhs = self.lower_expression(right_operand)?;
        let res_ty = match self.node_value_type(node_id)? {
            Some(ty) => ty,
            None => value_ty.clone(),
        };

        let result = self.emit_value_instr(
            IRInstructionKind::Binary {
                op,
                lhs: current,
                rhs,
            },
            res_ty,
        );

        self.emit_store(result.clone(), ptr)?;
        Ok(result)
    }

    pub fn lower_if_expr(&mut self, node: &IfExprNode) -> LowerResult<IRValue> {
        let cond = self.lower_expression(&node.condition)?;

        // Convert i8 bool to i1 for conditional branch using trunc
        let bool_cond = match cond.get_type() {
            IRType::I8 => {
                // Truncate i8 to i1
                self.emit_value_instr(
                    IRInstructionKind::Cast {
                        op: IRCastOp::Trunc,
                        value: cond,
                        to_type: IRType::I1,
                    },
                    IRType::I1,
                )
            }
            IRType::I1 => cond,
            other => {
                return Err(LowerError::TypeMismatch {
                    expected: IRType::I8,
                    found: other,
                });
            }
        };

        let then_label = self.fresh_label("if_then");
        let merge_label = self.fresh_label("if_merge");
        let else_label = node
            .else_block
            .as_ref()
            .map(|_| self.fresh_label("if_else"));

        let false_label = else_label.clone().unwrap_or(merge_label.clone());
        self.emit_void_instr(IRInstructionKind::CondBr {
            cond: bool_cond,
            then_dest: then_label.clone(),
            else_dest: false_label.clone(),
        });
        self.start_new_block(then_label.clone());
        let then_value = self.lower_block(&node.then_block)?;
        // Record the exit label for the then block
        let then_exit_label = self.current_block.label.clone();
        if !self.has_terminated() {
            self.emit_void_instr(IRInstructionKind::Br {
                dest: merge_label.clone(),
            });
        }
        let mut incoming = Vec::new();
        if let Some(then_val) = then_value {
            if then_val.get_type() != IRType::Void {
                incoming.push((then_val, then_exit_label));
            }
        }
        if let Some(else_block) = &node.else_block {
            let else_label = else_label.unwrap();
            self.start_new_block(else_label.clone());
            let else_value = match else_block {
                ElseBodyNode::Block(block) => self.lower_block(block)?,
                ElseBodyNode::If(if_expr) => Some(self.lower_if_expr(&if_expr)?),
            };
            let else_exit_label = self.current_block.label.clone();
            if !self.has_terminated() {
                self.emit_void_instr(IRInstructionKind::Br {
                    dest: merge_label.clone(),
                });
            }
            if let Some(else_val) = else_value {
                if else_val.get_type() != IRType::Void {
                    incoming.push((else_val, else_exit_label));
                }
            }
        }

        self.start_new_block(merge_label.clone());
        if incoming.is_empty() {
            Ok(IRValue::Undef(IRType::Void))
        } else if incoming.len() == 1 {
            Ok(incoming[0].0.clone())
        } else {
            let res_ty = incoming[0].0.get_type();
            let phi = self.emit_value_instr(
                IRInstructionKind::Phi {
                    ty: res_ty.clone(),
                    incomings: incoming,
                },
                res_ty,
            );
            Ok(phi)
        }
    }

    pub fn lower_while_expr(&mut self, node: &WhileExprNode) -> LowerResult<IRValue> {
        let cond_label = self.fresh_label("while_cond");
        let body_label = self.fresh_label("while_body");
        let exit_label = self.fresh_label("while_exit");

        self.emit_void_instr(IRInstructionKind::Br {
            dest: cond_label.clone(),
        });
        // Condition block
        self.start_new_block(cond_label.clone());
        let cond_val = self.lower_expression(&node.condition)?;

        // Convert i8 bool to i1 for conditional branch using trunc
        let bool_cond = match cond_val.get_type() {
            IRType::I8 => self.emit_value_instr(
                IRInstructionKind::Cast {
                    op: IRCastOp::Trunc,
                    value: cond_val,
                    to_type: IRType::I1,
                },
                IRType::I1,
            ),
            IRType::I1 => cond_val,
            other => {
                return Err(LowerError::TypeMismatch {
                    expected: IRType::I8,
                    found: other,
                });
            }
        };

        self.emit_void_instr(IRInstructionKind::CondBr {
            cond: bool_cond,
            then_dest: body_label.clone(),
            else_dest: exit_label.clone(),
        });

        // Body block
        self.start_new_block(body_label.clone());
        let loop_result_ty = self.node_value_type(node.node_id)?;
        self.loop_stack.push(LoopFrame::new(
            exit_label.clone(),
            cond_label.clone(),
            loop_result_ty,
        ));
        self.lower_block(&node.body)?;
        if !self.has_terminated() {
            self.emit_void_instr(IRInstructionKind::Br {
                dest: cond_label.clone(),
            });
        }
        let frame = self.loop_stack.pop().unwrap();

        // Exit block
        self.start_new_block(exit_label.clone());
        let loop_value = self.finish_loop_value(frame);
        Ok(loop_value)
    }

    pub fn lower_loop_expr(&mut self, node: &LoopExprNode) -> LowerResult<IRValue> {
        let header_label = self.fresh_label("loop_header");
        let body_label = self.fresh_label("loop_body");
        let exit_label = self.fresh_label("loop_exit");

        self.emit_void_instr(IRInstructionKind::Br {
            dest: header_label.clone(),
        });
        // Header block
        self.start_new_block(header_label.clone());
        self.emit_void_instr(IRInstructionKind::Br {
            dest: body_label.clone(),
        });
        // Body block
        self.start_new_block(body_label.clone());
        let loop_result_ty = self.node_value_type(node.node_id)?;
        self.loop_stack.push(LoopFrame::new(
            exit_label.clone(),
            header_label.clone(),
            loop_result_ty,
        ));
        self.lower_block(&node.body)?;
        if !self.has_terminated() {
            self.emit_void_instr(IRInstructionKind::Br {
                dest: header_label.clone(),
            });
        }

        let frame = self.loop_stack.pop().unwrap();
        // Exit block
        self.start_new_block(exit_label.clone());
        let loop_value = self.finish_loop_value(frame);
        Ok(loop_value)
    }

    pub fn lower_break_expr(&mut self, node: &BreakExprNode) -> LowerResult<IRValue> {
        let (expected_ty, break_label) = {
            let frame = self.loop_stack.last().ok_or_else(|| {
                LowerError::UnsupportedExpression("break statement outside of loop".to_string())
            })?;
            (frame.result_ty.clone(), frame.break_label.clone())
        };

        let mut break_value = if let Some(expr) = &node.value {
            let val = self.lower_expression(expr)?;
            Some(val)
        } else {
            None
        };

        if let Some(ty) = &expected_ty {
            if let Some(ref mut val) = break_value {
                if val.get_type() != *ty {
                    return Err(LowerError::TypeMismatch {
                        expected: ty.clone(),
                        found: val.get_type(),
                    });
                }
            }
        }

        let origin_label = self.current_block.label.clone();
        if let Some(frame) = self.loop_stack.last_mut() {
            if let Some(result_ty) = &frame.result_ty {
                let value = break_value
                    .take()
                    .unwrap_or_else(|| IRValue::Undef(result_ty.clone()));
                frame.break_values.push((value, origin_label));
            }
        }
        self.set_terminator(IRInstructionKind::Br { dest: break_label });
        Ok(IRValue::Undef(IRType::Void))
    }

    pub fn lower_continue_expr(&mut self, _node: &ContinueExprNode) -> LowerResult<IRValue> {
        let continue_label = {
            let frame = self.loop_stack.last().ok_or_else(|| {
                LowerError::UnsupportedExpression("continue statement outside of loop".to_string())
            })?;
            frame.continue_label.clone()
        };
        self.set_terminator(IRInstructionKind::Br {
            dest: continue_label,
        });
        Ok(IRValue::Undef(IRType::Void))
    }

    pub fn lower_as_expr(&mut self, node: &AsExprNode) -> LowerResult<IRValue> {
        let operand = self.lower_expression(&node.expr)?;
        let res_ty = match self.node_value_type(node.node_id) {
            Ok(Some(ty)) => ty,
            Ok(None) => {
                return Err(LowerError::MissingType(node.node_id));
            }
            Err(e) => return Err(e),
        };

        if operand.get_type() == res_ty {
            return Ok(operand);
        }

        match determine_cast_op(&operand.get_type(), &res_ty) {
            Ok(Some(op)) => {
                let casted = self.emit_value_instr(
                    IRInstructionKind::Cast {
                        op,
                        value: operand,
                        to_type: res_ty.clone(),
                    },
                    res_ty,
                );
                Ok(casted)
            }
            Ok(None) => Err(LowerError::UnsupportedExpression(format!(
                "cannot cast from {:?} to {:?}",
                operand.get_type(),
                res_ty,
            ))),
            Err(e) => Err(e),
        }
    }

    pub fn finish_loop_value(&mut self, frame: LoopFrame) -> IRValue {
        let LoopFrame {
            result_ty,
            break_values,
            ..
        } = frame;

        match result_ty {
            Some(ty) => {
                if matches!(ty, IRType::Void) {
                    IRValue::Undef(IRType::Void)
                } else {
                    if break_values.is_empty() {
                        IRValue::Undef(ty)
                    } else if break_values.len() == 1 {
                        break_values[0].0.clone()
                    } else {
                        self.emit_value_instr(
                            IRInstructionKind::Phi {
                                ty: ty.clone(),
                                incomings: break_values,
                            },
                            ty,
                        )
                    }
                }
            }
            None => IRValue::Undef(IRType::Void),
        }
    }
    pub fn lower_short_circuit(
        &mut self,
        node_id: NodeId,
        left: &ExpressionNode,
        right: &ExpressionNode,
        is_or: bool,
    ) -> LowerResult<IRValue> {
        let left_val = self.lower_expression(left)?;
        if left_val.get_type() != IRType::I8 {
            return Err(LowerError::TypeMismatch {
                expected: IRType::I8,
                found: left_val.get_type(),
            });
        }

        // Convert i8 to i1 for conditional branch using trunc
        let left_i1 = self.emit_value_instr(
            IRInstructionKind::Cast {
                op: IRCastOp::Trunc,
                value: left_val.clone(),
                to_type: IRType::I1,
            },
            IRType::I1,
        );

        let rhs_label = self.fresh_label("rhs");
        let merge_label = self.fresh_label("logic_merge");

        let current_block_label = self.current_block.label.clone();
        self.emit_void_instr(IRInstructionKind::CondBr {
            cond: left_i1,
            then_dest: if is_or {
                merge_label.clone()
            } else {
                rhs_label.clone()
            },
            else_dest: if is_or {
                rhs_label.clone()
            } else {
                merge_label.clone()
            },
        });

        // RHS block
        self.start_new_block(rhs_label.clone());
        let right_val = self.lower_expression(right)?;
        if right_val.get_type() != IRType::I8 {
            return Err(LowerError::TypeMismatch {
                expected: IRType::I8,
                found: right_val.get_type(),
            });
        }
        let rhs_exit_label = self.current_block.label.clone();
        if !self.has_terminated() {
            self.emit_void_instr(IRInstructionKind::Br {
                dest: merge_label.clone(),
            });
        }

        // Merge block
        self.start_new_block(merge_label.clone());

        let res_ty = match self.node_value_type(node_id) {
            Ok(Some(ty)) => ty,
            Ok(None) => IRType::I8, // Default to I8 for bool
            Err(e) => return Err(e),
        };
        let short_const = IRValue::ConstInt {
            value: if is_or { 1 } else { 0 },
            ty: res_ty.clone(),
        };
        let incoming_left = if is_or {
            (short_const.clone(), current_block_label.clone())
        } else {
            (left_val.clone(), current_block_label.clone())
        };
        let incoming_right = (right_val.clone(), rhs_exit_label);
        let phi = self.emit_value_instr(
            IRInstructionKind::Phi {
                ty: res_ty.clone(),
                incomings: vec![incoming_left, incoming_right],
            },
            res_ty,
        );

        Ok(phi)
    }

    fn fresh_label(&mut self, prefix: &str) -> String {
        let label = format!("{}_{}", prefix, self.temp_counter);
        self.temp_counter += 1;
        label
    }

    fn start_new_block(&mut self, label: String) {
        let finished = std::mem::replace(
            &mut self.current_block,
            IRBasicBlock {
                label,
                instructions: Vec::new(),
                terminator: None,
            },
        );
        self.blocks.push(finished);
    }

    pub fn lower_return(&mut self, ret: &ReturnExprNode) -> LowerResult<()> {
        if let Some(sret) = self.sret_ptr.clone() {
            if let Some(expr) = &ret.value {
                let value = self.lower_expression(expr)?;
                self.emit_store(value, sret)?;
            } else {
                return Err(LowerError::MissingReturnValue(
                    self.func.name.lexeme.clone(),
                ));
            }
            self.emit_return(None);
            return Ok(());
        }

        if matches!(self.return_type, IRType::Void) {
            if let Some(expr) = &ret.value {
                self.lower_expression(expr)?;
            }
            self.emit_return(None);
            return Ok(());
        }

        let value = if let Some(expr) = &ret.value {
            self.lower_expression(expr)?
        } else {
            return Err(LowerError::MissingReturnValue(
                self.func.name.lexeme.clone(),
            ));
        };
        let coerced = self.coerce_to_return_type(value)?;
        self.emit_return(Some(coerced));
        Ok(())
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
                // Check if we can use memset optimization for zero values
                let use_memset = length > 16
                    && matches!(elem_ty, IRType::I8 | IRType::I32)
                    && Self::is_zero_value(element);

                if use_memset {
                    // Calculate total bytes
                    let elem_size = match elem_ty {
                        IRType::I8 => 1,
                        IRType::I32 => 4,
                        _ => unreachable!(),
                    };
                    let total_bytes = length * elem_size;

                    // Cast array pointer to i8*
                    let i8_ptr = self.emit_value_instr(
                        IRInstructionKind::Cast {
                            op: IRCastOp::BitCast,
                            value: dest_ptr.clone(),
                            to_type: IRType::Ptr(Box::new(IRType::I8)),
                        },
                        IRType::Ptr(Box::new(IRType::I8)),
                    );

                    // Call llvm.memset
                    self.emit_void_instr(IRInstructionKind::Call {
                        callee: CallTarget::Direct("llvm.memset.p0.i32".to_string()),
                        args: vec![
                            i8_ptr,
                            IRValue::ConstInt {
                                value: 0,
                                ty: IRType::I8,
                            },
                            IRValue::ConstInt {
                                value: total_bytes as i64,
                                ty: IRType::I32,
                            },
                            IRValue::ConstInt {
                                value: 0,
                                ty: IRType::I1,
                            },
                        ],
                    });

                    return Ok(());
                }

                // Fall back to element-by-element store
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

    fn block_uses_identifier(block: &BlockNode, name: &str) -> bool {
        for stmt in &block.stats {
            if Self::statement_uses_identifier(stmt, name) {
                return true;
            }
        }
        if let Some(expr) = &block.final_expr {
            return Self::expr_uses_identifier(expr, name);
        }
        false
    }

    fn statement_uses_identifier(stmt: &StatementNode, name: &str) -> bool {
        match stmt {
            StatementNode::Let(node) => node
                .value
                .as_ref()
                .map_or(false, |expr| Self::expr_uses_identifier(expr, name)),
            StatementNode::Assign(node) => {
                node.identifier.lexeme == name || Self::expr_uses_identifier(&node.value, name)
            }
            StatementNode::Expression(expr_stmt) => {
                Self::expr_uses_identifier(&expr_stmt.expression, name)
            }
            StatementNode::Block(block) => Self::block_uses_identifier(block, name),
            StatementNode::Const(node) => Self::expr_uses_identifier(&node.value, name),
            StatementNode::Func(_) | StatementNode::Struct(_) => false,
        }
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
        // Memcpy optimization for Load+Store of large aggregates
        // Check if we're storing a value that was just loaded from another aggregate
        if let IRValue::InstructionRef { id, ty } = &value {
            if matches!(ty, IRType::Struct { .. } | IRType::Array { .. }) {
                let size = Self::calculate_type_size(ty);
                if size >= 16 {
                    // Find if this is from a Load instruction
                    if let Some(src_ptr) = self.find_load_source(id) {
                        // Use memcpy instead of storing the loaded value
                        // Note: We keep the Load instruction as it might be used elsewhere
                        // LLVM will optimize away redundant loads if needed
                        self.emit_memcpy(ptr, src_ptr, ty)?;
                        return Ok(());
                    }
                }
            }
        }

        self.emit_void_instr(IRInstructionKind::Store {
            value,
            ptr,
            align: None,
        });
        Ok(())
    }

    fn find_load_source(&self, id: &str) -> Option<IRValue> {
        // Search backwards through instructions to find the Load that produced this value
        for instr in self.current_block.instructions.iter().rev() {
            if let Some(res) = &instr.result {
                if let IRValue::InstructionRef { id: res_id, .. } = res {
                    if res_id == id {
                        if let IRInstructionKind::Load { ptr, .. } = &instr.kind {
                            return Some(ptr.clone());
                        }
                        return None; // Found the instruction but it's not a Load
                    }
                }
            }
        }
        None
    }

    fn emit_memcpy(&mut self, dest: IRValue, src: IRValue, ty: &IRType) -> LowerResult<()> {
        let size = Self::calculate_type_size(ty);

        // Cast dest to i8*
        let dest_i8 = self.emit_value_instr(
            IRInstructionKind::Cast {
                op: IRCastOp::BitCast,
                value: dest,
                to_type: IRType::Ptr(Box::new(IRType::I8)),
            },
            IRType::Ptr(Box::new(IRType::I8)),
        );

        // Cast src to i8*
        let src_i8 = self.emit_value_instr(
            IRInstructionKind::Cast {
                op: IRCastOp::BitCast,
                value: src,
                to_type: IRType::Ptr(Box::new(IRType::I8)),
            },
            IRType::Ptr(Box::new(IRType::I8)),
        );

        let size_val = IRValue::ConstInt {
            value: size as i64,
            ty: IRType::I32,
        };

        let volatile = IRValue::ConstInt {
            value: 0,
            ty: IRType::I1,
        };

        self.emit_void_instr(IRInstructionKind::Call {
            callee: CallTarget::Direct("llvm.memcpy.p0.p0.i32".to_string()),
            args: vec![dest_i8, src_i8, size_val, volatile],
        });
        Ok(())
    }
    pub fn emit_return(&mut self, value: Option<IRValue>) {
        let inst = IRInstruction {
            result: None,
            ty: value.as_ref().map(|v| v.get_type()),
            kind: IRInstructionKind::Ret { value },
            debug: None,
        };
        self.current_block.terminator = Some(inst);
    }
    pub fn bind_value(&mut self, name: String, binding: Binding) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name, binding);
        }
    }

    pub fn rebind_value(&mut self, name: String, binding: Binding) {
        for scope in self.scopes.iter_mut().rev() {
            if scope.contains_key(&name) {
                scope.insert(name, binding);
                return;
            }
        }
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name, binding);
        }
    }

    pub fn lower_struct_field_ptr(&mut self, member: &MemberExprNode) -> LowerResult<IRValue> {
        let object_ptr = self.lower_lvalue_pointer(&member.object)?;
        let Some(object_id) = expression_node_id(&member.object) else {
            return Err(LowerError::UnsupportedExpression(
                "cannot determine struct type for member access".to_string(),
            ));
        };
        let object_ty = self
            .type_ctx
            .get_type(object_id)
            .ok_or(LowerError::MissingType(object_id))?;
        let struct_name = match object_ty {
            RxType::Struct(name) => name.clone(),
            RxType::Ref(inner, _) => match inner.as_ref() {
                RxType::Struct(name) => name.clone(),
                other => {
                    return Err(LowerError::UnsupportedExpression(format!(
                        "cannot access member of non-struct type: {:?}",
                        other
                    )));
                }
            },
            other => {
                return Err(LowerError::UnsupportedExpression(format!(
                    "cannot access member of non-struct type: {:?}",
                    other
                )));
            }
        };

        let layout = self
            .type_ctx
            .get_struct_layout(&struct_name)
            .ok_or_else(|| {
                LowerError::UnsupportedExpression(format!("unknown struct type: {}", &struct_name))
            })?;

        let field_name = member.field.lexeme.as_str();
        let (index, field_layout) = layout
            .fields
            .iter()
            .enumerate()
            .find(|(_, f)| f.name == field_name)
            .ok_or_else(|| {
                LowerError::UnsupportedExpression(format!(
                    "struct {} has no field named {}",
                    &struct_name, field_name
                ))
            })?;
        let field_ty = rx_to_ir_type(self.type_ctx, &field_layout.ty);
        let (gep_base, _) = match object_ptr.get_type() {
            IRType::Ptr(inner) => match inner.as_ref() {
                IRType::Struct { .. } => Ok((object_ptr.clone(), inner.as_ref().clone())),
                IRType::Ptr(pointee) => match pointee.as_ref() {
                    IRType::Struct { .. } => {
                        let loaded = self.emit_value_instr(
                            IRInstructionKind::Load {
                                ptr: object_ptr.clone(),
                                align: None,
                            },
                            IRType::Ptr(pointee.clone()),
                        );
                        Ok((loaded, pointee.as_ref().clone()))
                    }
                    other => Err(LowerError::UnsupportedExpression(format!(
                        "cannot access member of non-struct type: {:?}",
                        other
                    ))),
                },
                other => Err(LowerError::UnsupportedExpression(format!(
                    "cannot access member of non-struct type: {:?}",
                    other
                ))),
            },
            other => Err(LowerError::UnsupportedExpression(format!(
                "cannot access member of non-pointer type: {:?}",
                other
            ))),
        }?;

        let res_ty = IRType::Ptr(Box::new(field_ty));
        let gep = self.emit_value_instr(
            IRInstructionKind::GetElementPtr {
                base: gep_base,
                indices: vec![const_i32(0), const_i32(index as i64)],
                in_bounds: true,
            },
            res_ty,
        );
        Ok(gep)
    }
    fn coerce_to_return_type(&mut self, value: IRValue) -> LowerResult<IRValue> {
        if value.get_type() == self.return_type {
            return Ok(value);
        }

        let value_ty = value.get_type().clone();
        if matches!(value, IRValue::Undef(_)) {
            return Ok(IRValue::Undef(self.return_type.clone()));
        }

        Err(LowerError::UnsupportedExpression(format!(
            "cannot coerce return value from {:?} to {:?}, the value is {:?}",
            value_ty, self.return_type, value
        )))
    }

    // Lower an expression expected to yield an lvalue pointer
    // return the pointer to the lvalue
    pub fn lower_lvalue_pointer(&mut self, expr: &ExpressionNode) -> LowerResult<IRValue> {
        match expr {
            ExpressionNode::Identifier(token, _) => {
                let binding = self
                    .lookup_binding(&token.lexeme)
                    .ok_or_else(|| LowerError::UndefinedIdentifier(token.lexeme.clone()))?;
                match binding {
                    Binding::Pointer(ptr) => Ok(ptr),
                    Binding::Value(val) => match val.get_type() {
                        IRType::Ptr(_) => Ok(val),
                        IRType::Struct { .. } | IRType::Array { .. } => {
                            let ty = val.get_type();
                            let ptr_ty = IRType::Ptr(Box::new(ty.clone()));
                            let alloca = self.emit_value_instr(
                                IRInstructionKind::Alloca {
                                    alloc_type: ty,
                                    align: None,
                                },
                                ptr_ty.clone(),
                            );
                            self.emit_store(val.clone(), alloca.clone())?;
                            self.rebind_value(
                                token.lexeme.clone(),
                                Binding::Pointer(alloca.clone()),
                            );
                            Ok(alloca)
                        }
                        _ => Err(LowerError::ImmutableBinding(token.lexeme.clone())),
                    },
                }
            }
            ExpressionNode::Member(member) => self.lower_struct_field_ptr(member),
            ExpressionNode::Index(index) => self.lower_array_index_ptr(index),
            ExpressionNode::Deref(node) => self.lower_expression(&node.operand),
            _ => Err(LowerError::UnsupportedExpression(
                "expression is not an lvalue".to_string(),
            )),
        }
    }

    pub fn lower_array_index_ptr(&mut self, index: &IndexExprNode) -> LowerResult<IRValue> {
        let base_ptr = self.lower_lvalue_pointer(&index.array)?;
        let index_val = self.lower_expression(&index.index)?;
        let Some(array_id) = expression_node_id(&index.array) else {
            return Err(LowerError::UnsupportedExpression(
                "cannot determine array type for indexing".to_string(),
            ));
        };

        let element_ty = if let Some(array_layout) = self.type_ctx.get_array_layout(array_id) {
            array_layout.elem_type.clone()
        } else {
            let array_ty = self
                .type_ctx
                .get_type(array_id)
                .ok_or(LowerError::MissingType(array_id))?;
            match array_ty {
                RxType::Array(elem, _) => elem.as_ref().clone(),
                RxType::Ref(inner, _) => match inner.as_ref() {
                    RxType::Array(elem, _) => elem.as_ref().clone(),
                    other => {
                        return Err(LowerError::UnsupportedExpression(format!(
                            "cannot index into non-array type: {:?}",
                            other
                        )));
                    }
                },
                other => {
                    return Err(LowerError::UnsupportedExpression(format!(
                        "cannot index into non-array type: {:?}",
                        other
                    )));
                }
            }
        };
        let elem_ir_ty = rx_to_ir_type(self.type_ctx, &element_ty);
        let base_ty = base_ptr.get_type();
        let indices = match base_ty {
            IRType::Ptr(inner) => match inner.as_ref() {
                IRType::Array { .. } => vec![const_i32(0), index_val.clone()],
                _ => vec![index_val.clone()],
            },
            other => {
                return Err(LowerError::UnsupportedExpression(format!(
                    "cannot index into non-pointer type: {:?}",
                    other
                )));
            }
        };
        let res_ty = IRType::Ptr(Box::new(elem_ir_ty));
        let gep = self.emit_value_instr(
            IRInstructionKind::GetElementPtr {
                base: base_ptr,
                indices,
                in_bounds: true,
            },
            res_ty,
        );
        Ok(gep)
    }

    fn prepare_method_receiver(
        &mut self,
        object: &ExpressionNode,
        expected_rx: &RxType,
    ) -> LowerResult<IRValue> {
        let expected_ir = rx_to_ir_type(self.type_ctx, expected_rx);
        if matches!(expected_rx, RxType::Ref(_, _)) {
            if let Ok(ptr) = self.lower_lvalue_pointer(object) {
                return Ok(self.ensure_pointer_type(ptr, expected_ir)?);
            }
            let value = self.lower_expression(object)?;
            if value.get_type() == expected_ir {
                return Ok(value);
            }
            let inner_ty = match &expected_ir {
                IRType::Ptr(inner) => inner.as_ref().clone(),
                _ => value.get_type().clone(),
            };
            let alloca = self.emit_value_instr(
                IRInstructionKind::Alloca {
                    alloc_type: inner_ty.clone(),
                    align: None,
                },
                IRType::Ptr(Box::new(inner_ty.clone())),
            );
            self.emit_store(value, alloca.clone())?;
            Ok(self.ensure_pointer_type(alloca, expected_ir)?)
        } else {
            let value = self.lower_expression(object)?;
            if value.get_type() == expected_ir {
                Ok(value)
            } else if matches!(value.get_type(), IRType::Ptr(_))
                && matches!(expected_ir, IRType::Ptr(_))
            {
                Ok(self.ensure_pointer_type(value, expected_ir)?)
            } else {
                Err(LowerError::TypeMismatch {
                    expected: expected_ir,
                    found: value.get_type(),
                })
            }
        }
    }

    fn adjust_binary_op(&self, op: IRBinaryOp, node_id: NodeId) -> IRBinaryOp {
        let Some(rx_type) = self.type_ctx.get_type(node_id) else {
            return op;
        };
        if !is_unsigned_integer_type(&rx_type) {
            return op;
        }
        match op {
            IRBinaryOp::SDiv => IRBinaryOp::UDiv,
            IRBinaryOp::SRem => IRBinaryOp::URem,
            IRBinaryOp::AShr => IRBinaryOp::LShr,
            other => other,
        }
    }

    fn adjust_compare_op(
        &self,
        op: IRICmpOp,
        token: &TokenType,
        lhs: &ExpressionNode,
    ) -> LowerResult<IRICmpOp> {
        let Some(lhs_id) = expression_node_id(lhs) else {
            return Err(LowerError::UnsupportedExpression(
                "cannot determine type for comparison".to_string(),
            ));
        };
        let Some(rx_type) = self.type_ctx.get_type(lhs_id) else {
            return Err(LowerError::MissingType(lhs_id));
        };
        if !is_unsigned_integer_type(&rx_type) {
            return Ok(op);
        }
        match token {
            TokenType::Gt => Ok(IRICmpOp::Ugt),
            TokenType::GEq => Ok(IRICmpOp::Uge),
            TokenType::Lt => Ok(IRICmpOp::Ult),
            TokenType::LEq => Ok(IRICmpOp::Ule),
            _ => Ok(op),
        }
    }

    fn ensure_pointer_type(&mut self, ptr: IRValue, expected_ty: IRType) -> LowerResult<IRValue> {
        if ptr.get_type() == expected_ty {
            Ok(ptr)
        } else {
            return Err(LowerError::TypeMismatch {
                expected: expected_ty,
                found: ptr.get_type(),
            });
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn set_terminator(&mut self, kind: IRInstructionKind) {
        self.current_block.terminator = Some(IRInstruction::new(kind));
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

    fn lookup_binding(&self, name: &str) -> Option<Binding> {
        for scope in self.scopes.iter().rev() {
            if let Some(binding) = scope.get(name) {
                return Some(binding.clone());
            }
        }
        None
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
    break_values: Vec<(IRValue, String)>,
}

impl LoopFrame {
    pub fn new(break_label: String, continue_label: String, result_ty: Option<IRType>) -> Self {
        Self {
            break_label,
            continue_label,
            result_ty,
            break_values: Vec::new(),
        }
    }
}
