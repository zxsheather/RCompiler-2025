use std::{collections::HashMap, usize};

use crate::frontend::{
    r_lexer::token::{Token, TokenType},
    r_parser::ast::{
        ArrayLiteralNode, AsExprNode, AssignStatementNode, AstNode, BinaryExprNode, BlockNode,
        BreakExprNode, CallExprNode, ConstItemNode, ContinueExprNode, DerefExprNode, ElseBodyNode,
        ExprStatementNode, ExpressionNode, FunctionNode, IfExprNode, ImplNode, ImplTraitBlockNode,
        IndexExprNode, LetStatementNode, LoopExprNode, MemberExprNode, MethodCallExprNode,
        RefExprNode, ReturnExprNode, StatementNode, StaticMemberExprNode, StructDeclNode,
        StructLiteralNode, TraitDeclNode, TypeNode, UnaryExprNode, WhileExprNode,
    },
    r_semantic::{
        built_in::{get_built_in_funcs, get_built_in_methods, get_built_in_static_methods},
        const_folder::ConstFolder,
        error::{SemanticError, SemanticResult},
        tyctxt::TypeContext,
        types::{RxType, RxValue},
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
    consts: HashMap<String, (RxType, RxValue)>,
    funcs: HashMap<String, FuncSig>,
}

impl Scope {
    fn declare_var(&mut self, symbol: Symbol) {
        self.vars.insert(symbol.name.clone(), symbol);
    }

    fn get(&self, name: &str) -> Option<&Symbol> {
        self.vars.get(name)
    }

    fn declare_const(&mut self, name: &str, ty: RxType, val: RxValue) {
        self.consts.insert(name.to_string(), (ty, val));
    }

    fn get_const(&self, name: &str) -> Option<&(RxType, RxValue)> {
        self.consts.get(name)
    }

    fn declare_fn(&mut self, name: String, sig: FuncSig) {
        self.funcs.insert(name, sig);
    }

    fn get_fn(&self, name: &str) -> Option<&FuncSig> {
        self.funcs.get(name)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncSig {
    param_types: Vec<RxType>,
    return_type: RxType,
    token: Token,
    self_kind: SelfKind,
}

impl FuncSig {
    pub fn new(param_types: Vec<RxType>, return_type: RxType, self_kind: SelfKind) -> Self {
        Self {
            param_types,
            return_type,
            token: Token::default(),
            self_kind,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum SelfKind {
    None,
    Owned { ty: RxType },
    Borrowed { ty: RxType },
    BorrowedMut { ty: RxType },
    TraitOwned,
    TraitBorrowed,
    TraitBorrowedMut,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Globe {
    scope_stack: Vec<Scope>,
    // funcs: HashMap<String, FuncSig>,
    structs: HashMap<String, HashMap<String, RxType>>,
    methods: HashMap<(String, String), FuncSig>, // (struct, method) -> sig
    static_methods: HashMap<(String, String), FuncSig>, // no self
    traits: HashMap<String, HashMap<String, FuncSig>>, // trait -> method -> sig
    impl_traits: HashMap<String, Vec<String>>,   // struct -> traits
    // const_items: HashMap<String, (RxType, RxValue)>, // name -> (type, value)
    enums: HashMap<String, HashMap<String, usize>>, // enum -> (name, index)
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

    fn declare_const(&mut self, name: &Token, ty: &RxType, val: &RxValue) -> SemanticResult<()> {
        if let Some(scope) = self.scope_stack.last_mut() {
            if scope.get_const(&name.lexeme).is_some() {
                return Err(SemanticError::ConstRedeclaration {
                    name: name.lexeme.clone(),
                    line: name.position.line,
                    column: name.position.column,
                });
            }
            scope.declare_const(&name.lexeme, ty.clone(), val.clone());
        } else {
            return Err(SemanticError::DeclarationOutOfScope {
                name: name.lexeme.clone(),
                line: name.position.line,
                column: name.position.column,
            });
        }
        Ok(())
    }

    pub fn lookup_var(&self, name: &str) -> Option<&Symbol> {
        for scope in self.scope_stack.iter().rev() {
            if let Some(s) = scope.get(name) {
                return Some(s);
            }
        }
        None
    }

    pub fn lookup_const(&self, name: &str) -> Option<&(RxType, RxValue)> {
        for scope in self.scope_stack.iter().rev() {
            if let Some(c) = scope.get_const(name) {
                return Some(c);
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
        let sig = FuncSig {
            param_types: params,
            return_type: ret,
            token: tok,
            self_kind: SelfKind::None,
        };
        if let Some(scope) = self.scope_stack.last_mut() {
            if scope.get_fn(&name).is_some() {
                return Err(SemanticError::FunctionRedeclaration {
                    name,
                    line: sig.token.position.line,
                    column: sig.token.position.column,
                });
            }
            scope.declare_fn(name, sig);
        } else {
            return Err(SemanticError::DeclarationOutOfScope {
                name,
                line: sig.token.position.line,
                column: sig.token.position.column,
            });
        }
        Ok(())
    }

    fn get_var_or_const_type(&self, name: &str) -> Option<RxType> {
        if let Some(var) = self.lookup_var(name) {
            Some(var.ty.clone())
        } else if let Some(c) = self.lookup_const(name) {
            Some(c.0.clone())
        } else {
            None
        }
    }

    fn lookup_fn(&self, name: &str) -> Option<&FuncSig> {
        for scope in self.scope_stack.iter().rev() {
            if let Some(f) = scope.get_fn(name) {
                return Some(f);
            }
        }
        None
    }
}

pub struct Analyzer {
    pub globe: Globe,
    pub type_context: TypeContext,
    current_return_type: Option<RxType>,
    loop_stack: Vec<LoopContext>,
    current_struct: Option<String>,
}

pub struct LoopContext {
    pub expected_type: Option<RxType>,
    pub allow_value: bool,
}

impl Analyzer {
    pub fn new() -> Self {
        Self {
            globe: Globe::default(),
            type_context: TypeContext::new(),
            current_return_type: None,
            loop_stack: Vec::new(),
            current_struct: None,
        }
    }

    fn add_built_ins(&mut self) -> SemanticResult<()> {
        // built-in functions
        for (name, sig) in get_built_in_funcs() {
            self.globe.declare_fn(
                name.to_string(),
                sig.param_types,
                sig.return_type,
                sig.token.clone(),
            )?;
        }

        // built in structs
        self.globe.structs.insert("String".into(), HashMap::new());
        self.globe.structs.insert("U32".into(), HashMap::new());
        self.globe.structs.insert("USize".into(), HashMap::new());
        self.globe.structs.insert("Str".into(), HashMap::new());
        self.globe.structs.insert("Array".into(), HashMap::new());

        // built-in methods
        for (ty, name, sig) in get_built_in_methods() {
            self.globe
                .methods
                .insert((ty.into(), name.into()), sig.clone());
        }

        // built-in static methods
        for (ty, name, sig) in get_built_in_static_methods() {
            self.globe
                .static_methods
                .insert((ty.into(), name.into()), sig.clone());
        }

        Ok(())
    }

    pub fn analyse_program(&mut self, nodes: &[AstNode]) -> SemanticResult<()> {
        self.globe.push_scope();
        self.add_built_ins()?;
        for node in nodes {
            match node {
                AstNode::Statement(stmt) => {
                    if let StatementNode::Const(_) = stmt {
                        self.analyse_statement(stmt)?;
                    }
                }
                _ => {
                    // Do nothing in this pass
                }
            }
        }
        for node in nodes {
            match node {
                AstNode::Function(func) => {
                    let sig = self.extract_sig(func)?;
                    self.globe.declare_fn(
                        sig.token.lexeme.clone(),
                        sig.param_types,
                        sig.return_type,
                        sig.token,
                    )?;
                }
                AstNode::Struct(sd) => {
                    self.analyse_struct_decl(sd)?;
                }
                AstNode::Trait(td) => {
                    self.declare_trait(td)?;
                }
                AstNode::Enum(ed) => {
                    let mut enum_map = HashMap::new();
                    for (i, var) in ed.variants.iter().enumerate() {
                        enum_map.insert(var.name.lexeme.clone(), i);
                    }
                    self.globe.enums.insert(ed.name.lexeme.clone(), enum_map);
                }
                _ => {
                    // Do nothing in this pass
                }
            }
        }

        for node in nodes {
            match node {
                AstNode::Impl(impl_node) => {
                    self.analyse_impl_struct(impl_node)?;
                }
                AstNode::ImplTrait(it) => {
                    self.analyse_impl_trait(it)?;
                }
                _ => {
                    // Nothing to do in this pass
                }
            }
        }

        for node in nodes {
            match node {
                AstNode::Function(func) => {
                    self.analyse_function(func)?;
                }

                AstNode::Impl(i) => {
                    self.current_struct = Some(i.name.lexeme.clone());
                    for m in i.methods.iter() {
                        self.analyse_function(m)?;
                    }
                    self.current_struct = None;
                }

                AstNode::Statement(stmt) => {
                    if let StatementNode::Const(_) = stmt {
                        continue;
                    }
                    self.globe.push_scope();
                    self.analyse_statement(stmt)?;
                    self.globe.pop_scope();
                }

                AstNode::Expression(expr) => {
                    self.globe.push_scope();
                    self.analyse_expression(expr)?;
                    self.globe.pop_scope();
                }

                _ => {
                    // Nothing to do in this pass
                }
            }
        }
        self.globe.pop_scope();
        Ok(())
    }

    fn extract_sig(&mut self, func: &FunctionNode) -> SemanticResult<FuncSig> {
        let name = func.name.lexeme.clone();
        let params: Vec<RxType> = func
            .param_list
            .params
            .iter()
            .map(|p| self.type_from_ann(p.type_annotation.as_ref(), &p.name))
            .collect::<SemanticResult<Vec<_>>>()?;
        let mut ret = match &func.return_type {
            Some(t) => self.type_from_node(t)?,
            None => RxType::Unit,
        };

        if name.as_str() == "main" {
            if !params.is_empty() {
                return Err(SemanticError::MainFunctionSignatureInvalid {
                    line: func.name.position.line,
                    column: func.name.position.column,
                });
            }
            if ret != RxType::Unit {
                return Err(SemanticError::MainFunctionSignatureInvalid {
                    line: func.name.position.line,
                    column: func.name.position.column,
                });
            }
            ret = RxType::MainReturn;
        }

        Ok(FuncSig {
            param_types: params,
            return_type: ret,
            token: func.name.clone(),
            self_kind: SelfKind::None,
        })
    }

    pub fn declare_trait(&mut self, td: &TraitDeclNode) -> SemanticResult<()> {
        let mut methods = HashMap::new();
        for m in &td.methods {
            // Temporarily requires parameters containing self
            if m.param_list.params.is_empty()
                || !matches!(m.param_list.params[0].name.token_type, TokenType::SelfLower)
            {
                return Err(SemanticError::TraitMethodSignatureMismatch {
                    trait_name: td.name.lexeme.clone(),
                    type_name: "<unknown>".to_string(),
                    method: m.name.lexeme.clone(),
                    detail: "first parameter must be 'self'".to_string(),
                    line: m.name.position.line,
                    column: m.name.position.column,
                });
            }

            let mut param_types = Vec::new();
            for p in m.param_list.params.iter().skip(1) {
                let ty = self.type_from_ann(p.type_annotation.as_ref(), &p.name)?;
                param_types.push(ty);
            }
            let return_type = match &m.return_type {
                Some(t) => self.type_from_node(t)?,
                None => RxType::Unit,
            };
            let trait_self_kind = if let Some(first_param) = m.param_list.params.first() {
                match &first_param.type_annotation {
                    Some(TypeNode::SelfRef { mutable }) => {
                        if *mutable {
                            SelfKind::TraitBorrowedMut
                        } else {
                            SelfKind::TraitBorrowed
                        }
                    }
                    Some(TypeNode::Named(tok)) if tok.lexeme == td.name.lexeme => {
                        SelfKind::TraitOwned
                    }
                    None => SelfKind::TraitOwned,
                    _ => SelfKind::TraitOwned,
                }
            } else {
                SelfKind::TraitOwned
            };
            methods.insert(
                m.name.lexeme.clone(),
                FuncSig {
                    param_types,
                    return_type,
                    token: m.name.clone(),
                    self_kind: trait_self_kind,
                },
            );
        }
        self.globe.traits.insert(td.name.lexeme.clone(), methods);
        Ok(())
    }

    fn analyse_struct_decl(&mut self, sd: &StructDeclNode) -> SemanticResult<()> {
        let mut field_map = HashMap::new();
        for field in &sd.fields {
            let ty = self.type_from_node(&field.type_annotation)?;
            field_map.insert(field.name.lexeme.clone(), ty);
        }
        self.globe.structs.insert(sd.name.lexeme.clone(), field_map);
        self.globe
            .impl_traits
            .insert(sd.name.lexeme.clone(), Vec::new());
        Ok(())
    }

    fn analyse_impl_struct(&mut self, impl_node: &ImplNode) -> SemanticResult<()> {
        let st_name = impl_node.name.lexeme.clone();
        self.current_struct = Some(st_name.clone());
        if !self.globe.structs.contains_key(&st_name) {
            return Err(SemanticError::UnknownStruct {
                name: st_name,
                line: impl_node.name.position.line,
                column: impl_node.name.position.column,
            });
        }
        for m in &impl_node.methods {
            let mut param_types = Vec::new();
            for p in m.param_list.params.iter() {
                let ty = self.type_from_ann(p.type_annotation.as_ref(), &p.name)?;
                param_types.push(ty);
            }
            let return_type = match &m.return_type {
                Some(t) => self.type_from_node(t)?,
                None => RxType::Unit,
            };

            let is_instance = m
                .param_list
                .params
                .first()
                .map(|p| matches!(p.name.token_type, TokenType::SelfLower))
                .unwrap_or(false);
            if is_instance {
                let self_ty = param_types.get(0).cloned().unwrap();
                // Determine self_kind and validate matches impl type
                let self_kind = match &self_ty {
                    RxType::Struct(s) if *s == st_name => SelfKind::Owned {
                        ty: RxType::Struct(st_name.clone()),
                    },
                    RxType::Ref(inner, is_mut) => match &**inner {
                        RxType::Struct(s) if *s == st_name => {
                            if *is_mut {
                                SelfKind::BorrowedMut {
                                    ty: RxType::Struct(st_name.clone()),
                                }
                            } else {
                                SelfKind::Borrowed {
                                    ty: RxType::Struct(st_name.clone()),
                                }
                            }
                        }
                        other => {
                            return Err(SemanticError::Generic {
                                msg: format!(
                                    "self type in impl must be {} or &/&mut {}, found {}",
                                    st_name, st_name, other
                                ),
                                line: m.name.position.line,
                                column: m.name.position.column,
                            });
                        }
                    },
                    other => {
                        return Err(SemanticError::Generic {
                            msg: format!(
                                "self type in impl must be {} or &/&mut {}, found {}",
                                st_name, st_name, other
                            ),
                            line: m.name.position.line,
                            column: m.name.position.column,
                        });
                    }
                };
                let mut rest_params = param_types.clone();
                rest_params.remove(0);
                self.globe.methods.insert(
                    (st_name.clone(), m.name.lexeme.clone()),
                    FuncSig {
                        param_types: rest_params,
                        return_type,
                        token: m.name.clone(),
                        self_kind,
                    },
                );
            } else {
                self.globe.static_methods.insert(
                    (st_name.clone(), m.name.lexeme.clone()),
                    FuncSig {
                        param_types,
                        return_type,
                        token: m.name.clone(),
                        self_kind: SelfKind::None,
                    },
                );
            }
        }
        self.current_struct = None;
        Ok(())
    }

    fn analyse_impl_trait(&mut self, it: &ImplTraitBlockNode) -> SemanticResult<()> {
        if !self.globe.traits.contains_key(&it.trait_name.lexeme) {
            return Err(SemanticError::UnknownTrait {
                name: it.trait_name.lexeme.clone(),
                line: it.trait_name.position.line,
                column: it.trait_name.position.column,
            });
        }

        if !self.globe.structs.contains_key(&it.type_name.lexeme) {
            return Err(SemanticError::UnknownTrait {
                name: it.type_name.lexeme.clone(),
                line: it.type_name.position.line,
                column: it.type_name.position.column,
            });
        }

        self.current_struct = Some(it.type_name.lexeme.clone());

        let mut methods = HashMap::new();
        // Currently only support struct.method
        for m in &it.methods {
            if m.param_list.params.is_empty()
                || !matches!(m.param_list.params[0].name.token_type, TokenType::SelfLower)
            {
                return Err(SemanticError::TraitMethodSignatureMismatch {
                    trait_name: it.trait_name.lexeme.clone(),
                    type_name: it.type_name.lexeme.clone(),
                    method: m.name.lexeme.clone(),
                    detail: "first parameter must be 'self'".to_string(),
                    line: m.name.position.line,
                    column: m.name.position.column,
                });
            }

            let self_kind = if let Some(self_param) = m.param_list.params.first() {
                if let Some(ann) = &self_param.type_annotation {
                    let self_ty = self.type_from_node(ann)?;
                    match &self_ty {
                        RxType::Struct(s) if *s == it.type_name.lexeme => SelfKind::Owned {
                            ty: RxType::Struct(it.type_name.lexeme.clone()),
                        },
                        RxType::Ref(inner, is_mut) => match &**inner {
                            RxType::Struct(s) if *s == it.type_name.lexeme => {
                                if *is_mut {
                                    SelfKind::BorrowedMut {
                                        ty: RxType::Struct(it.type_name.lexeme.clone()),
                                    }
                                } else {
                                    SelfKind::Borrowed {
                                        ty: RxType::Struct(it.type_name.lexeme.clone()),
                                    }
                                }
                            }
                            other => {
                                return Err(SemanticError::Generic {
                                    msg: format!(
                                        "self type in trait impl must be {} or &/&mut {}, found {}",
                                        it.type_name.lexeme, it.type_name.lexeme, other
                                    ),
                                    line: m.name.position.line,
                                    column: m.name.position.column,
                                });
                            }
                        },
                        other => {
                            return Err(SemanticError::Generic {
                                msg: format!(
                                    "self type in trait impl must be {} or &/&mut {}, found {}",
                                    it.type_name.lexeme, it.type_name.lexeme, other
                                ),
                                line: m.name.position.line,
                                column: m.name.position.column,
                            });
                        }
                    }
                } else {
                    // No annotation => treat as owned
                    SelfKind::Owned {
                        ty: RxType::Struct(it.type_name.lexeme.clone()),
                    }
                }
            } else {
                unreachable!("checked is_empty above");
            };

            let mut param_types = Vec::new();
            for p in m.param_list.params.iter().skip(1) {
                let ty = self.type_from_ann(p.type_annotation.as_ref(), &p.name)?;
                param_types.push(ty);
            }
            let return_type = match &m.return_type {
                Some(ty) => self.type_from_node(ty)?,
                None => RxType::Unit,
            };
            methods.insert(
                m.name.lexeme.clone(),
                FuncSig {
                    param_types,
                    return_type,
                    token: m.name.clone(),
                    self_kind,
                },
            );
        }
        let trait_methods = self
            .globe
            .traits
            .get(&it.trait_name.lexeme)
            .expect("checked above");
        self.validate_trait_impl(
            &it.trait_name.lexeme,
            &it.type_name.lexeme,
            trait_methods,
            &methods,
        )?;

        let traits = self
            .globe
            .impl_traits
            .get_mut(&it.type_name.lexeme)
            .expect("checked above");
        if traits.contains(&it.trait_name.lexeme) {
            return Err(SemanticError::DuplicatedTraitImpl {
                trait_name: it.trait_name.lexeme.clone(),
                type_name: it.type_name.lexeme.clone(),
                line: it.trait_name.position.line,
                column: it.trait_name.position.column,
            });
        }
        traits.push(it.trait_name.lexeme.clone());

        // Register concrete impl trait methods as regular methods so that
        // method dispatch (and self kind checking) uses concrete self_kind.
        for (name, sig) in methods.into_iter() {
            self.globe
                .methods
                .insert((it.type_name.lexeme.clone(), name), sig);
        }

        self.current_struct = None;

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
                mutable: param.mutable,
                token: param.name.clone(),
            })?;
        }
        let mut ret_ty = func
            .return_type
            .as_ref()
            .map(|t| self.type_from_node(t))
            .transpose()?
            .unwrap_or(RxType::Unit);
        if self.globe.scope_stack.len() == 2 && func.name.lexeme == "main" {
            if !param_types.is_empty() {
                return Err(SemanticError::MainFunctionSignatureInvalid {
                    line: func.name.position.line,
                    column: func.name.position.column,
                });
            }
            if ret_ty != RxType::Unit {
                return Err(SemanticError::MainFunctionSignatureInvalid {
                    line: func.name.position.line,
                    column: func.name.position.column,
                });
            }
            ret_ty = RxType::MainReturn;
        }
        self.current_return_type = Some(ret_ty.clone());
        let blk_ty = self.analyse_block(&func.body)?;
        if RxType::unify(&ret_ty, &blk_ty).is_none() {
            if ret_ty == RxType::MainReturn && blk_ty == RxType::Unit {
                // allow main to return () implicitly
            } else {
                return Err(SemanticError::FunctionReturnTypeMismatch {
                    name: func.name.lexeme.clone(),
                    expected: ret_ty,
                    found: blk_ty,
                    line: func.name.position.line,
                    column: func.name.position.column,
                });
            }
        }
        self.globe.pop_scope();
        Ok(())
    }

    pub fn analyse_block(&mut self, blk: &BlockNode) -> SemanticResult<RxType> {
        self.globe.push_scope();
        let mut ret = RxType::Unit;
        let mut exit_flag = false;
        for stmt in blk.stats.iter() {
            match stmt {
                StatementNode::Const(_) => {
                    self.analyse_statement(stmt)?;
                }
                _ => {}
            }
        }
        for stmt in blk.stats.iter() {
            match stmt {
                StatementNode::Func(func) => {
                    let sig = self.extract_sig(func)?;
                    self.globe.declare_fn(
                        sig.token.lexeme.clone(),
                        sig.param_types,
                        sig.return_type,
                        sig.token,
                    )?;
                }
                StatementNode::Struct(_) => {
                    self.analyse_statement(stmt)?;
                }
                _ => {}
            }
        }
        for stmt in blk.stats.iter() {
            match stmt {
                StatementNode::Func(_) => {
                    self.analyse_statement(stmt)?;
                }
                _ => {}
            }
        }
        for stmt in blk.stats.iter() {
            if exit_flag {
                return Err(SemanticError::Generic {
                    msg: "Unreachable code".into(),
                    line: 0,
                    column: 0,
                });
            }
            if matches!(
                stmt,
                StatementNode::Const(_) | StatementNode::Func(_) | StatementNode::Struct(_)
            ) {
                continue;
            }
            let ty = self.analyse_statement(stmt)?;
            if let Some(t) = ty {
                if t.is_never() {
                    ret = RxType::Never;
                    break;
                }

                if matches!(t, RxType::MainReturn) {
                    ret = RxType::MainReturn;
                    exit_flag = true;
                }
            }
        }
        if let Some(expr) = &blk.final_expr {
            if exit_flag {
                return Err(SemanticError::Generic {
                    msg: "Unreachable code".into(),
                    line: 0,
                    column: 0,
                });
            }
            ret = self.analyse_expression(expr)?;
        }
        self.globe.pop_scope();
        Ok(ret)
    }

    // If the stat is expr stat, return the type of expr
    pub fn analyse_statement(&mut self, stmt: &StatementNode) -> SemanticResult<Option<RxType>> {
        match stmt {
            StatementNode::Let(LetStatementNode {
                let_token,
                mutable,
                identifier,
                type_annotation,
                value,
                ..
            }) => {
                let mut expr_ty = if let Some(val) = value {
                    self.analyse_expression(val)?
                } else {
                    RxType::Never
                };
                if let Some(ty) = type_annotation {
                    let decl_ty = self.type_from_node(&ty)?;
                    match RxType::unify(&decl_ty, &expr_ty) {
                        Some(unified) => {
                            expr_ty = unified;
                        }
                        None => {
                            return Err(SemanticError::AssignTypeMismatched {
                                expected: decl_ty,
                                found: expr_ty,
                                line: let_token.position.line,
                                column: let_token.position.column,
                            });
                        }
                    }
                }
                if matches!(identifier.token_type, TokenType::Underscore) {
                    return Ok(None);
                }
                self.globe.declare_var(Symbol {
                    ty: expr_ty,
                    name: identifier.lexeme.clone(),
                    mutable: *mutable,
                    token: identifier.clone(),
                })?;
                Ok(None)
            }
            StatementNode::Assign(AssignStatementNode {
                identifier, value, ..
            }) => {
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
                if RxType::unify(&symbol.ty, &value_ty).is_none() {
                    return Err(SemanticError::AssignTypeMismatched {
                        expected: symbol.ty,
                        found: value_ty,
                        line: identifier.position.line,
                        column: identifier.position.column,
                    });
                }
                Ok(None)
            }
            StatementNode::Const(ConstItemNode {
                const_token,
                name,
                type_annotation,
                value,
                ..
            }) => {
                let decl_ty = self.type_from_node(&type_annotation)?;
                let (value_ty, const_val) = ConstFolder::calc_expr(
                    &value,
                    const_token,
                    &self.globe,
                    &mut self.type_context,
                )?;
                if RxType::unify(&decl_ty, &value_ty).is_none() {
                    return Err(SemanticError::AssignTypeMismatched {
                        expected: decl_ty,
                        found: value_ty,
                        line: const_token.position.line,
                        column: const_token.position.column,
                    });
                }
                self.globe.declare_const(name, &decl_ty, &const_val)?;
                Ok(None)
            }
            StatementNode::Struct(sd) => {
                self.analyse_struct_decl(sd)?;
                Ok(None)
            }
            StatementNode::Block(b) => {
                let ty = self.analyse_block(b)?;
                Ok(Some(ty))
            }
            // Handled later
            StatementNode::Func(func) => {
                self.analyse_function(func)?;
                Ok(None)
            }
            StatementNode::Expression(ExprStatementNode { expression, .. }) => {
                let ty = self.analyse_expression(expression)?;
                Ok(Some(ty))
            }
        }
    }

    pub fn analyse_expression(&mut self, expr: &ExpressionNode) -> SemanticResult<RxType> {
        match expr {
            ExpressionNode::Identifier(token, node_id) => {
                if let Some(ty) = self.globe.get_var_or_const_type(&token.lexeme) {
                    self.type_context.set_type(*node_id, ty.clone());
                    Ok(ty.clone())
                } else {
                    Err(SemanticError::UndefinedIdentifier {
                        name: token.lexeme.clone(),
                        line: token.position.line,
                        column: token.position.column,
                    })
                }
            }
            ExpressionNode::IntegerLiteral(token, node_id) => {
                let (ty, _) = ConstFolder::parse_int_literal(token)?;
                self.type_context.set_type(*node_id, ty.clone());
                Ok(ty)
            }
            ExpressionNode::StringLiteral(_, node_id) => {
                self.type_context
                    .set_type(*node_id, RxType::Ref(Box::new(RxType::Str), false));
                Ok(RxType::Ref(Box::new(RxType::Str), false))
            }
            ExpressionNode::CharLiteral(_, node_id) => {
                self.type_context.set_type(*node_id, RxType::Char);
                Ok(RxType::Char)
            }
            ExpressionNode::BoolLiteral(_, node_id) => {
                self.type_context.set_type(*node_id, RxType::Bool);
                Ok(RxType::Bool)
            }
            ExpressionNode::Block(b) => Ok(self.analyse_block(b)?),
            ExpressionNode::ArrayLiteral(arr) => Ok(self.analyse_array_literal(arr)?),
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
            ExpressionNode::Loop(l) => Ok(self.analyse_loop(l)?),
            ExpressionNode::Break(brk) => Ok(self.analyse_break(brk)?),
            ExpressionNode::Continue(ctn) => Ok(self.analyse_continue(ctn)?),
            ExpressionNode::Call(c) => Ok(self.analyse_call(c)?),
            ExpressionNode::MethodCall(mc) => Ok(self.analyse_method_call(mc)?),
            ExpressionNode::Member(m) => Ok(self.analyse_member(m)?),
            ExpressionNode::StructLiteral(sl) => Ok(self.analyse_struct_literal(sl)?),
            ExpressionNode::StaticMember(sm) => Ok(self.analyse_static_member(sm)?),
            ExpressionNode::Ref(r) => Ok(self.analyse_ref(r)?),
            ExpressionNode::Deref(d) => Ok(self.analyse_deref(d)?),
            ExpressionNode::Return(ret) => Ok(self.analyse_return(ret)?),
            ExpressionNode::As(a) => Ok(self.analyse_as(a)?),
            ExpressionNode::Underscore(..) => Ok(RxType::Never),
        }
    }

    fn analyse_unary(&mut self, u: &UnaryExprNode) -> SemanticResult<RxType> {
        let rt = self.analyse_expression(&u.operand)?;
        match &u.operator.token_type {
            TokenType::Plus | TokenType::Minus => {
                if rt.is_integer() {
                    self.type_context.set_type(u.node_id, rt.clone());
                    Ok(rt)
                } else {
                    Err(SemanticError::InvalidUnaryOperandType {
                        expected_type: "numeric type".to_string(),
                        found_type: format!("{}", rt),
                        line: u.operator.position.line,
                        column: u.operator.position.column,
                    })
                }
            }
            TokenType::Not => {
                if !matches!(rt, RxType::Bool) && !rt.is_integer() {
                    Err(SemanticError::InvalidUnaryOperandType {
                        expected_type: "bool or numeric type".to_string(),
                        found_type: format!("{}", rt),
                        line: u.operator.position.line,
                        column: u.operator.position.column,
                    })
                } else {
                    self.type_context.set_type(u.node_id, rt.clone());
                    Ok(rt)
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
                } else {
                    if let Some(unified) = RxType::unify(&lt, &rt) {
                        self.type_context.set_type(b.node_id, unified.clone());
                        Ok(unified)
                    } else {
                        Err(SemanticError::MismatchedBinaryTypes {
                            op: op_token.as_str().to_string(),
                            left: lt,
                            right: rt,
                            line,
                            column,
                        })
                    }
                }
            }

            SL | SR => {
                if !lt.is_integer() {
                    Err(SemanticError::ArityMismatch {
                        operator: op_token.as_str().to_string(),
                        expected_type: "numeric type".to_string(),
                        found: lt,
                        line,
                        column,
                    })
                } else if !rt.is_integer() {
                    Err(SemanticError::ArityMismatch {
                        operator: op_token.as_str().to_string(),
                        expected_type: "i32".to_string(),
                        found: rt,
                        line,
                        column,
                    })
                } else {
                    self.type_context.set_type(b.node_id, lt.clone());
                    Ok(lt)
                }
            }

            EqEq | NEq => {
                if let Some(_) = RxType::unify(&lt, &rt) {
                    self.type_context.set_type(b.node_id, RxType::Bool);
                    Ok(RxType::Bool)
                } else {
                    Err(SemanticError::MismatchedBinaryTypes {
                        op: op_token.as_str().to_string(),
                        left: lt,
                        right: rt,
                        line,
                        column,
                    })
                }
            }

            Lt | LEq | Gt | GEq => {
                if !lt.is_integer() {
                    Err(SemanticError::ArityMismatch {
                        operator: op_token.as_str().to_string(),
                        expected_type: "numeric type".to_string(),
                        found: lt,
                        line,
                        column,
                    })
                } else if RxType::unify(&lt, &rt).is_none() {
                    Err(SemanticError::MismatchedBinaryTypes {
                        op: op_token.as_str().to_string(),
                        left: lt,
                        right: rt,
                        line,
                        column,
                    })
                } else {
                    self.type_context.set_type(b.node_id, RxType::Bool);
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
                    self.type_context.set_type(b.node_id, RxType::Bool);
                    Ok(RxType::Bool)
                }
            }

            PlusEq | MinusEq | MulEq | DivEq | ModEq | AndEq | OrEq | XorEq | SLEq | SREq => {
                // Treat as: l = l <op> r
                if !self.is_mutable_lvalue(&b.left_operand) {
                    return Err(SemanticError::AssignImmutableVar {
                        name: "<expr>".to_string(),
                        line,
                        column,
                    });
                }
                // For now require integer arithmetic just like simple + - * /
                if !lt.is_integer() {
                    return Err(SemanticError::ArityMismatch {
                        operator: op_token.as_str().to_string(),
                        expected_type: "numeric type".to_string(),
                        found: lt,
                        line,
                        column,
                    });
                }
                if let Some(unified) = RxType::unify(&lt, &rt) {
                    self.type_context.set_type(b.node_id, unified.clone());
                    Ok(unified)
                } else {
                    Err(SemanticError::MismatchedBinaryTypes {
                        op: op_token.as_str().to_string(),
                        left: lt,
                        right: rt,
                        line,
                        column,
                    })
                }
            }

            Eq => {
                if !self.is_mutable_lvalue(&b.left_operand) {
                    return Err(SemanticError::AssignImmutableVar {
                        name: "<expr>".to_string(),
                        line,
                        column,
                    });
                }
                if let Some(unified) = RxType::unify(&lt, &rt) {
                    self.type_context.set_type(b.node_id, unified.clone());
                    Ok(unified)
                } else {
                    Err(SemanticError::MismatchedBinaryTypes {
                        op: op_token.as_str().to_string(),
                        left: lt,
                        right: rt,
                        line,
                        column,
                    })
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
        let mut arr_ty = self.analyse_expression(&i.array)?;
        if let RxType::Ref(inner, _) = arr_ty.clone() {
            arr_ty = *inner;
        }
        let idx_ty = self.analyse_expression(&i.index)?;
        // TODO: Handle idx_ty later
        if RxType::unify(&idx_ty, &RxType::USize).is_none() {
            // Currently not handle position information
            return Err(SemanticError::InvalidIndexType {
                found: idx_ty,
                line: 0,
                column: 0,
            });
        }
        if let RxType::Array(elem, _) = arr_ty {
            self.type_context.set_type(i.node_id, (*elem).clone());
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
        let mut obj_ty = self.analyse_expression(&m.object)?;
        if let RxType::Ref(inner, _) = obj_ty.clone() {
            obj_ty = *inner;
        }
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

    fn analyse_static_member(&mut self, sm: &StaticMemberExprNode) -> SemanticResult<RxType> {
        if self.globe.structs.contains_key(&sm.type_name.lexeme) {
            return Ok(RxType::Unit);
        }
        if let Some(enum_map) = self.globe.enums.get(&sm.type_name.lexeme) {
            if let Some(_) = enum_map.get(&sm.member.lexeme) {
                return Ok(RxType::Struct(sm.type_name.lexeme.clone()));
            } else {
                return Err(SemanticError::UnknownEnumVariant {
                    enum_name: sm.type_name.lexeme.clone(),
                    variant: sm.member.lexeme.clone(),
                    line: sm.member.position.line,
                    column: sm.member.position.column,
                });
            }
        }
        return Err(SemanticError::UnknownStruct {
            name: sm.type_name.lexeme.clone(),
            line: sm.type_name.position.line,
            column: sm.type_name.position.column,
        });
    }

    fn analyse_deref(&mut self, d: &DerefExprNode) -> SemanticResult<RxType> {
        let ty = self.analyse_expression(&d.operand)?;
        match ty {
            RxType::Ref(inner, _) => Ok(*inner),
            _ => Err(SemanticError::Generic {
                msg: "Cannot dereference non-reference type".to_string(),
                line: d.star_token.position.line,
                column: d.star_token.position.column,
            }),
        }
    }

    fn analyse_ref(&mut self, r: &RefExprNode) -> SemanticResult<RxType> {
        let ty = self.analyse_expression(&r.operand)?;
        if r.mutable {
            match &*r.operand {
                ExpressionNode::IntegerLiteral(..)
                | ExpressionNode::StringLiteral(..)
                | ExpressionNode::CharLiteral(..)
                | ExpressionNode::BoolLiteral(..)
                | ExpressionNode::ArrayLiteral(..)
                | ExpressionNode::TupleLiteral(..)
                | ExpressionNode::StructLiteral(..) => {}
                ExpressionNode::Identifier(tok, ..) => {
                    let Some(symbol) = self.globe.lookup_var(&tok.lexeme) else {
                        return Err(SemanticError::UndefinedIdentifier {
                            name: tok.lexeme.clone(),
                            line: tok.position.line,
                            column: tok.position.column,
                        });
                    };
                    if !symbol.mutable {
                        return Err(SemanticError::BorrowMutFromImmutable {
                            name: tok.lexeme.clone(),
                            line: tok.position.line,
                            column: tok.position.column,
                        });
                    }
                }
                ExpressionNode::Index(IndexExprNode { array, .. }) => match &**array {
                    ExpressionNode::Identifier(tok, ..) => {
                        let Some(symbol) = self.globe.lookup_var(&tok.lexeme) else {
                            return Err(SemanticError::UndefinedIdentifier {
                                name: tok.lexeme.clone(),
                                line: tok.position.line,
                                column: tok.position.column,
                            });
                        };
                        let can_write = match &symbol.ty {
                            RxType::Ref(_, is_mut) => *is_mut,
                            _ => symbol.mutable,
                        };
                        if !can_write {
                            return Err(SemanticError::BorrowMutFromImmutable {
                                name: tok.lexeme.clone(),
                                line: tok.position.line,
                                column: tok.position.column,
                            });
                        }
                    }
                    ExpressionNode::Member(MemberExprNode { object, .. }) => {
                        if let ExpressionNode::Identifier(tok, ..) = &**object {
                            let Some(symbol) = self.globe.lookup_var(&tok.lexeme) else {
                                return Err(SemanticError::UndefinedIdentifier {
                                    name: tok.lexeme.clone(),
                                    line: tok.position.line,
                                    column: tok.position.column,
                                });
                            };
                            let can_write = match &symbol.ty {
                                RxType::Ref(_, is_mut) => *is_mut,
                                _ => symbol.mutable,
                            };
                            if !can_write {
                                return Err(SemanticError::BorrowMutFromImmutable {
                                    name: tok.lexeme.clone(),
                                    line: tok.position.line,
                                    column: tok.position.column,
                                });
                            }
                        } else {
                            return Err(SemanticError::Generic {
                                msg: "Cannot take mutable reference of non-lvalue".to_string(),
                                line: r.ref_token.position.line,
                                column: r.ref_token.position.column,
                            });
                        }
                    }
                    _ => {
                        return Err(SemanticError::Generic {
                            msg: "Cannot take mutable reference of non-lvalue".to_string(),
                            line: r.ref_token.position.line,
                            column: r.ref_token.position.column,
                        });
                    }
                },
                ExpressionNode::Member(MemberExprNode { object, .. }) => {
                    if let ExpressionNode::Identifier(tok, ..) = &**object {
                        let Some(symbol) = self.globe.lookup_var(&tok.lexeme) else {
                            return Err(SemanticError::UndefinedIdentifier {
                                name: tok.lexeme.clone(),
                                line: tok.position.line,
                                column: tok.position.column,
                            });
                        };
                        let can_write = match &symbol.ty {
                            RxType::Ref(_, is_mut) => *is_mut,
                            _ => symbol.mutable,
                        };
                        if !can_write {
                            return Err(SemanticError::BorrowMutFromImmutable {
                                name: tok.lexeme.clone(),
                                line: tok.position.line,
                                column: tok.position.column,
                            });
                        }
                    } else {
                        return Err(SemanticError::Generic {
                            msg: "Cannot take mutable reference of non-lvalue".to_string(),
                            line: r.ref_token.position.line,
                            column: r.ref_token.position.column,
                        });
                    }
                }
                _ => {
                    return Err(SemanticError::Generic {
                        msg: "Cannot take mutable reference of rvalue".to_string(),
                        line: 0,
                        column: 0,
                    });
                }
            }
        }
        self.type_context
            .set_type(r.node_id, RxType::Ref(Box::new(ty.clone()), r.mutable));
        Ok(RxType::Ref(Box::new(ty), r.mutable))
    }

    fn analyse_array_literal(&mut self, arr: &ArrayLiteralNode) -> SemanticResult<RxType> {
        match arr {
            ArrayLiteralNode::Elements { elements, node_id } => {
                let mut elem_ty = if let Some(node) = elements.first() {
                    self.analyse_expression(node)?
                } else {
                    RxType::Unit
                };
                for elem in elements.iter() {
                    let tp = self.analyse_expression(elem)?;
                    elem_ty = match RxType::unify(&tp, &elem_ty) {
                        Some(unified) => unified,
                        None => {
                            return Err(SemanticError::MixedTypedArray {
                                type1: tp,
                                type2: elem_ty,
                            });
                        }
                    };
                }
                self.type_context.set_type(
                    *node_id,
                    RxType::Array(Box::new(elem_ty.clone()), Some(elements.len())),
                );
                Ok(RxType::Array(Box::new(elem_ty), Some(elements.len())))
            }

            ArrayLiteralNode::Repeated {
                element,
                size,
                node_id,
            } => {
                let elem_ty = self.analyse_expression(element)?;
                let (_, size_val) = ConstFolder::calc_expr(
                    size,
                    &Token::default(),
                    &self.globe,
                    &mut self.type_context,
                )?;
                let size = size_val.as_usize()?;
                self.type_context.set_type(
                    *node_id,
                    RxType::Array(Box::new(elem_ty.clone()), Some(size)),
                );
                Ok(RxType::Array(Box::new(elem_ty), Some(size)))
            }
        }
    }

    fn analyse_return(&mut self, ret: &ReturnExprNode) -> SemanticResult<RxType> {
        if let Some(expected) = self.current_return_type.clone() {
            match (&ret.value, &expected) {
                (Some(val_expr), exp_ty) => {
                    let vty = self.analyse_expression(val_expr)?;
                    if RxType::unify(exp_ty, &vty).is_none() {
                        return Err(SemanticError::FunctionReturnTypeMismatch {
                            name: "<anonymous>".to_string(),
                            expected: exp_ty.clone(),
                            found: vty,
                            line: ret.return_token.position.line,
                            column: ret.return_token.position.column,
                        });
                    }
                }
                (None, exp_ty) => {
                    if RxType::unify(&expected, &RxType::Unit).is_none() {
                        return Err(SemanticError::FunctionReturnTypeMismatch {
                            name: "<anonymous>".to_string(),
                            expected: exp_ty.clone(),
                            found: RxType::Unit,
                            line: ret.return_token.position.line,
                            column: ret.return_token.position.column,
                        });
                    }
                }
            }
        } else {
            return Err(SemanticError::Generic {
                msg: "return outside function".to_string(),
                line: ret.return_token.position.line,
                column: ret.return_token.position.column,
            });
        }
        Ok(RxType::Never)
    }

    fn analyse_struct_literal(&mut self, s: &StructLiteralNode) -> SemanticResult<RxType> {
        let name = s.name.lexeme.clone();
        let line = s.name.position.line;
        let column = s.name.position.column;
        let Some(field_map) = self.globe.structs.get(&name).cloned() else {
            return Err(SemanticError::UnknownStruct { name, line, column });
        };
        if field_map.len() != s.fields.len() {
            return Err(SemanticError::Generic {
                msg: "struct field count mismatch".to_string(),
                line,
                column,
            });
        }
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
            if RxType::unify(&found, expected).is_none() {
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

    fn analyse_as(&mut self, a: &AsExprNode) -> SemanticResult<RxType> {
        let expr_ty = self.analyse_expression(&a.expr)?;
        if !expr_ty.is_integer() && !matches!(expr_ty, RxType::Char | RxType::Bool) {
            return Err(SemanticError::Generic {
                msg: format!("Only integer, char, bool can be casted, found {}", expr_ty),
                line: a.as_token.position.line,
                column: a.as_token.position.column,
            });
        }
        let target_ty = self.type_from_node(&a.type_name)?;
        if !target_ty.is_integer() {
            return Err(SemanticError::Generic {
                msg: format!("Only integer can be casted to, found {}", target_ty),
                line: a.as_token.position.line,
                column: a.as_token.position.column,
            });
        }
        self.type_context.set_type(a.node_id, target_ty.clone());
        Ok(target_ty)
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
            Some(ElseBodyNode::Block(b)) => self.analyse_block(b)?,
            Some(ElseBodyNode::If(i)) => self.analyse_if(i)?,
            None => RxType::Unit,
        };
        if let Some(ty) = RxType::unify(&then_ty, &else_ty) {
            Ok(ty)
        } else {
            Err(SemanticError::BranchTypeMismatched {
                then_ty,
                else_ty,
                line,
                column,
            })
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
        self.loop_stack.push(LoopContext {
            expected_type: Some(RxType::Unit),
            allow_value: false,
        });
        self.analyse_block(&w.body)?;
        self.loop_stack.pop();
        self.type_context.set_type(w.node_id, RxType::Unit);
        Ok(RxType::Unit)
    }

    fn analyse_loop(&mut self, l: &LoopExprNode) -> SemanticResult<RxType> {
        self.loop_stack.push(LoopContext {
            expected_type: None,
            allow_value: true,
        });
        let body_ty = self.analyse_block(&l.body)?;
        let ctx = self.loop_stack.pop().unwrap();
        if body_ty == RxType::Never && ctx.expected_type.is_none() {
            self.type_context.set_type(l.node_id, RxType::Never);
            return Ok(RxType::Never);
        }
        // If no break encountered and body doesn't diverge -> infinite loop UB, treat as Never
        let ty = ctx.expected_type.unwrap_or(RxType::Never);
        self.type_context.set_type(l.node_id, ty.clone());
        Ok(ty)
    }

    fn analyse_break(&mut self, brk: &BreakExprNode) -> SemanticResult<RxType> {
        let break_value_ty = if let Some(val_expr) = &brk.value {
            Some(self.analyse_expression(val_expr)?)
        } else {
            None
        };
        let Some(ctx) = self.loop_stack.last_mut() else {
            return Err(SemanticError::Generic {
                msg: "break outside loop".to_string(),
                line: brk.break_token.position.line,
                column: brk.break_token.position.column,
            });
        };
        if !ctx.allow_value && brk.value.is_some() {
            return Err(SemanticError::Generic {
                msg: "break with value only allowed in 'loop'".to_string(),
                line: brk.break_token.position.line,
                column: brk.break_token.position.column,
            });
        }
        if let Some(vty) = break_value_ty {
            match &ctx.expected_type {
                Some(exp) => {
                    let new_tp = RxType::unify(&vty, exp);
                    if new_tp.is_none() {
                        return Err(SemanticError::Generic {
                            msg: format!("break value type mismatch: expected {exp}, found {vty}"),
                            line: brk.break_token.position.line,
                            column: brk.break_token.position.column,
                        });
                    } else {
                        ctx.expected_type = new_tp;
                    }
                }
                None => {
                    ctx.expected_type = Some(vty);
                }
            }
        } else {
            if ctx.allow_value {
                if ctx.expected_type.is_none() {
                    ctx.expected_type = Some(RxType::Unit);
                }
            }
        }
        Ok(RxType::Never)
    }

    fn analyse_continue(&mut self, ctn: &ContinueExprNode) -> SemanticResult<RxType> {
        if self.loop_stack.is_empty() {
            Err(SemanticError::Generic {
                msg: "continue outside loop".to_string(),
                line: ctn.continue_token.position.line,
                column: ctn.continue_token.position.column,
            })
        } else {
            Ok(RxType::Never)
        }
    }

    fn analyse_call(&mut self, c: &CallExprNode) -> SemanticResult<RxType> {
        match &*c.function {
            ExpressionNode::StaticMember(sm) => {
                let st = if matches!(sm.type_name.token_type, TokenType::SelfUpper) {
                    if let Some(current_struct) = &self.current_struct {
                        current_struct.clone()
                    } else {
                        return Err(SemanticError::Generic {
                            msg: "Self:: used outside struct".to_string(),
                            line: sm.type_name.position.line,
                            column: sm.type_name.position.column,
                        });
                    }
                } else {
                    sm.type_name.lexeme.clone()
                };
                let line = sm.type_name.position.line;
                let column = sm.type_name.position.column;
                if !self.globe.structs.contains_key(&st) {
                    return Err(SemanticError::UnknownStruct {
                        name: st,
                        line,
                        column,
                    });
                }
                let method_name = sm.member.lexeme.clone();
                let Some(sig) = self
                    .globe
                    .static_methods
                    .get(&(st.clone(), method_name.clone()))
                    .cloned()
                else {
                    return Err(SemanticError::UnknownCallee {
                        name: format!("{}::{}", sm.type_name.lexeme, method_name),
                        line: sm.member.position.line,
                        column: sm.member.position.column,
                    });
                };
                let line = sig.token.position.line;
                let column = sig.token.position.column;
                if sig.param_types.len() != c.args.len() {
                    return Err(SemanticError::ArgsNumMismatched {
                        callee: format!("{}::{}", st, method_name),
                        expected: sig.param_types.len(),
                        found: c.args.len(),
                        line,
                        column,
                    });
                }
                for (i, (pt, arg)) in sig.param_types.iter().zip(&c.args).enumerate() {
                    let at = self.analyse_expression(arg)?;
                    if RxType::unify(pt, &at).is_none() {
                        return Err(SemanticError::ArgTypeMismatched {
                            callee: format!("{}::{}", st, method_name),
                            index: i,
                            expected: pt.clone(),
                            found: at.clone(),
                            line,
                            column,
                        });
                    }
                }
                self.type_context
                    .set_type(c.node_id, sig.return_type.clone());
                Ok(sig.return_type)
            }
            ExpressionNode::Identifier(token, node_id) => {
                let callee_name = token.lexeme.clone();
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
                    if let ExpressionNode::IntegerLiteral(value, _) = arg {
                        let val = ConstFolder::calc_expr(
                            arg,
                            value,
                            &self.globe,
                            &mut self.type_context,
                        )?;
                        if let RxValue::IntLiteral(v) = val.1 {
                            if v >= i32::MAX as i64 {
                                return Err(SemanticError::Generic {
                                    msg: "Integer literal overflow".to_string(),
                                    line: value.position.line,
                                    column: value.position.column,
                                });
                            }
                        }
                    }
                    let at = self.analyse_expression(arg)?;
                    if RxType::unify(pt, &at).is_none() {
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
                self.type_context
                    .set_type(*node_id, sig.return_type.clone());
                Ok(sig.return_type)
            }
            _ => Err(SemanticError::Generic {
                msg: "Only simple function or method calls are supported".to_string(),
                line: 0,
                column: 0,
            }),
        }
    }

    fn analyse_method_call(&mut self, mc: &MethodCallExprNode) -> SemanticResult<RxType> {
        let obj_expr_ty = self.analyse_expression(&mc.object)?;
        let struct_name = match obj_expr_ty.clone() {
            RxType::Struct(s) => s,
            RxType::Ref(inner, _) => match *inner {
                RxType::Struct(s) => s,
                RxType::String => "String".to_string(),
                RxType::Array(..) => "Array".to_string(),
                RxType::Str => "str".to_string(),
                RxType::USize => "usize".to_string(),
                RxType::U32 => "u32".to_string(),
                RxType::IntLiteral => "u32".to_string(),
                other => {
                    return Err(SemanticError::Generic {
                        msg: format!("Method call receiver must be struct, found {}", other),
                        line: mc.method.position.line,
                        column: mc.method.position.column,
                    });
                }
            },
            RxType::String => "String".to_string(),
            RxType::Array(..) => "Array".to_string(),
            RxType::Str => "str".to_string(),
            RxType::USize => "usize".to_string(),
            RxType::U32 => "u32".to_string(),
            RxType::IntLiteral => "u32".to_string(),
            other => {
                return Err(SemanticError::Generic {
                    msg: format!("Method call receiver must be struct, found {}", other),
                    line: mc.method.position.line,
                    column: mc.method.position.column,
                });
            }
        };
        let method_name = mc.method.lexeme.clone();
        let key = obj_expr_ty.method_key();
        if key.is_empty() {
            return Err(SemanticError::Generic {
                msg: "Method call receiver must be struct or special type".to_string(),
                line: mc.method.position.line,
                column: mc.method.position.column,
            });
        }
        let sig = self
            .globe
            .methods
            .get(&(key.clone(), method_name.clone()))
            .cloned()
            .ok_or_else(|| SemanticError::UnknownCallee {
                name: format!("{}::{}", key, method_name),
                line: mc.method.position.line,
                column: mc.method.position.column,
            })?;
        let sig = if let Some(sig) = self
            .globe
            .methods
            .get(&(struct_name.clone(), method_name.clone()))
            .cloned()
        {
            sig
        } else {
            let mut found: Option<FuncSig> = None;
            for trait_name in self.globe.impl_traits.get(&struct_name).unwrap_or(&vec![]) {
                if let Some(sig) = self
                    .globe
                    .traits
                    .get(trait_name)
                    .unwrap_or(&HashMap::new())
                    .get(&method_name)
                    .cloned()
                {
                    found = Some(sig);
                    break;
                }
            }
            if let Some(sig) = found {
                sig
            } else {
                return Err(SemanticError::UnknownCallee {
                    name: format!("{}::{}", struct_name, method_name),
                    line: mc.method.position.line,
                    column: mc.method.position.column,
                });
            }
        };

        let (receiver_ok, expected_self_type) = match &sig.self_kind {
            SelfKind::Owned { ty } => {
                // allow owned T, &T, &mut T
                let mut base = obj_expr_ty.clone();
                if let RxType::Ref(inner, _) = base {
                    base = *inner;
                }
                if let Some(unified_ty) = RxType::unify(&base, ty) {
                    (true, unified_ty)
                } else {
                    (false, ty.clone())
                }
            }
            SelfKind::Borrowed { ty } => {
                let mut base = obj_expr_ty.clone();
                if let RxType::Ref(inner, _) = base {
                    base = *inner;
                }
                // owned T auto-borrows; for wildcard array treat any array as match
                let ok = match (&base, ty) {
                    (RxType::Array(_, _), RxType::Array(_, _)) => true,
                    _ => RxType::unify(&base, ty).is_some(),
                };
                (ok, RxType::Ref(Box::new(ty.clone()), false))
            }
            SelfKind::BorrowedMut { ty } => {
                // require either &mut T, or mutable owned lvalue T (auto &mut). Reject immutable.
                let base = obj_expr_ty.clone();
                if let RxType::Ref(inner, is_mut) = &obj_expr_ty {
                    if RxType::unify(&inner, ty).is_some() && *is_mut {
                        (true, RxType::Ref(Box::new(ty.clone()), true))
                    } else {
                        (false, RxType::Ref(Box::new(ty.clone()), true))
                    }
                } else {
                    // owned
                    let mut base2 = base.clone();
                    if let RxType::Ref(inner, _) = base2 {
                        base2 = *inner;
                    }
                    if RxType::unify(&base2, ty).is_some() {
                        (
                            self.is_mutable_lvalue(&mc.object),
                            RxType::Ref(Box::new(ty.clone()), true),
                        )
                    } else {
                        (false, RxType::Ref(Box::new(ty.clone()), true))
                    }
                }
            }
            _ => (true, RxType::Unit),
        };
        if !receiver_ok {
            return Err(SemanticError::ArgTypeMismatched {
                callee: format!("{}::{}", key, method_name),
                index: 0,
                expected: expected_self_type,
                found: obj_expr_ty,
                line: mc.method.position.line,
                column: mc.method.position.column,
            });
        }
        if sig.param_types.len() != mc.args.len() {
            return Err(SemanticError::ArgsNumMismatched {
                callee: format!("{}.{}", struct_name, method_name),
                expected: sig.param_types.len(),
                found: mc.args.len(),
                line: mc.method.position.line,
                column: mc.method.position.column,
            });
        }
        for (i, (pt, arg)) in sig.param_types.iter().zip(&mc.args).enumerate() {
            let at = self.analyse_expression(arg)?;
            if RxType::unify(pt, &at).is_none() {
                return Err(SemanticError::ArgTypeMismatched {
                    callee: format!("{}.{}", struct_name, method_name),
                    index: i + 1,
                    expected: pt.clone(),
                    found: at.clone(),
                    line: mc.method.position.line,
                    column: mc.method.position.column,
                });
            }
        }
        self.type_context
            .set_type(mc.node_id, sig.return_type.clone());
        Ok(sig.return_type)
    }

    fn is_mutable_lvalue(&self, expr: &ExpressionNode) -> bool {
        match expr {
            ExpressionNode::Identifier(tok, ..) => self
                .globe
                .lookup_var(&tok.lexeme)
                .map(|s| match &s.ty {
                    RxType::Ref(_, mutable) => *mutable,
                    _ => s.mutable,
                })
                .unwrap_or(false),
            ExpressionNode::Deref(DerefExprNode { operand, .. }) => self.is_mutable_lvalue(operand),
            ExpressionNode::Index(IndexExprNode { array, .. }) => self.is_mutable_lvalue(array),
            ExpressionNode::Member(MemberExprNode { object, .. }) => self.is_mutable_lvalue(object),
            _ => false,
        }
    }

    fn type_from_ann(
        &mut self,
        ann: Option<&TypeNode>,
        name_tok: &Token,
    ) -> SemanticResult<RxType> {
        match ann {
            Some(t) => self.type_from_node(t),
            None => Err(SemanticError::NeedAnnotation {
                name: name_tok.lexeme.clone(),
                line: name_tok.position.line,
                column: name_tok.position.column,
            }),
        }
    }

    fn type_from_node(&mut self, type_node: &TypeNode) -> SemanticResult<RxType> {
        Ok(match type_node {
            TypeNode::I32(_) => RxType::I32,
            TypeNode::U32(_) => RxType::U32,
            TypeNode::ISize(_) => RxType::ISize,
            TypeNode::USize(_) => RxType::USize,
            TypeNode::Bool(_) => RxType::Bool,
            TypeNode::String(_) => RxType::String,
            TypeNode::Unit => RxType::Unit,
            TypeNode::Str(_) => RxType::Str,
            TypeNode::Char(_) => RxType::Char,
            TypeNode::Tuple(tys) => {
                let mut rxtypes = Vec::with_capacity(tys.len());
                for ty in tys {
                    rxtypes.push(self.type_from_node(ty)?);
                }
                RxType::Tuple(rxtypes)
            }
            TypeNode::Array { elem_type, size } => {
                let elem_ty = self.type_from_node(&elem_type)?;
                let len = if let Some(size_expr) = size {
                    let (_, size_val) = ConstFolder::calc_expr(
                        size_expr,
                        &Token::default(),
                        &self.globe,
                        &mut self.type_context,
                    )?;
                    Some(size_val.as_usize()?)
                } else {
                    None
                };
                RxType::Array(Box::new(elem_ty), len)
            }
            TypeNode::Ref {
                inner_type,
                mutable,
            } => {
                let t = self.type_from_node(&inner_type)?;
                RxType::Ref(Box::new(t), *mutable)
            }
            TypeNode::SelfRef { mutable } => {
                return Err(SemanticError::Generic {
                    msg: format!(
                        "unexpected bare self reference type (mutable={mutable}) after desugaring"
                    ),
                    line: 0,
                    column: 0,
                });
            }
            TypeNode::Named(token) => {
                let name = token.lexeme.clone();
                if self.globe.structs.contains_key(&name) {
                    RxType::Struct(name)
                } else if self.globe.enums.contains_key(&name) {
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

    fn validate_trait_impl(
        &self,
        trait_name: &str,
        type_name: &str,
        trait_methods: &HashMap<String, FuncSig>,
        impl_methods: &HashMap<String, FuncSig>,
    ) -> SemanticResult<()> {
        for (name, trait_sig) in trait_methods {
            if let Some(impl_sig) = impl_methods.get(name) {
                if trait_sig.param_types != impl_sig.param_types {
                    return Err(SemanticError::TraitMethodSignatureMismatch {
                        trait_name: trait_name.to_string(),
                        type_name: type_name.to_string(),
                        method: name.clone(),
                        detail: format!(
                            "parameter types mismatch: expected {:?}, found {:?}",
                            trait_sig.param_types, impl_sig.param_types
                        ),
                        line: impl_sig.token.position.line,
                        column: impl_sig.token.position.column,
                    });
                }

                if trait_sig.return_type != impl_sig.return_type {
                    return Err(SemanticError::TraitMethodSignatureMismatch {
                        trait_name: trait_name.to_string(),
                        type_name: type_name.to_string(),
                        method: name.clone(),
                        detail: format!(
                            "return type mismatch: expected {:?}, found {:?}",
                            trait_sig.return_type, impl_sig.return_type
                        ),
                        line: impl_sig.token.position.line,
                        column: impl_sig.token.position.column,
                    });
                }
                // Ensure trait self kind matches impl self kind
                // Validate self kind compatibility
                let ok_self = match (&trait_sig.self_kind, &impl_sig.self_kind) {
                    (SelfKind::TraitOwned, SelfKind::Owned { .. }) => true,
                    (SelfKind::TraitBorrowed, SelfKind::Borrowed { .. }) => true,
                    (SelfKind::TraitBorrowedMut, SelfKind::BorrowedMut { .. }) => true,
                    _ => false,
                };
                if !ok_self {
                    return Err(SemanticError::TraitMethodSignatureMismatch {
                        trait_name: trait_name.to_string(),
                        type_name: type_name.to_string(),
                        method: name.clone(),
                        detail: format!(
                            "self kind mismatch: trait requires {:?}, impl provides {:?}",
                            trait_sig.self_kind, impl_sig.self_kind
                        ),
                        line: impl_sig.token.position.line,
                        column: impl_sig.token.position.column,
                    });
                }
            } else {
                return Err(SemanticError::MissingTraitImplMethod {
                    trait_name: trait_name.to_string(),
                    type_name: type_name.to_string(),
                    method: name.clone(),
                    line: trait_sig.token.position.line,
                    column: trait_sig.token.position.column,
                });
            }
        }

        for (name, impl_sig) in impl_methods {
            if !trait_methods.contains_key(name) {
                return Err(SemanticError::ImplMethodNotInTrait {
                    trait_name: trait_name.to_string(),
                    type_name: type_name.to_string(),
                    method: name.clone(),
                    line: impl_sig.token.position.line,
                    column: impl_sig.token.position.column,
                });
            }
        }
        Ok(())
    }
}
