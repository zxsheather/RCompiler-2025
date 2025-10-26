use std::{alloc::Layout, collections::HashMap};

use serde::de;

use crate::frontend::r_semantic::{
    analyzer::{SelfKind, Symbol},
    types::{RxType, RxValue},
};

pub type NodeId = usize;

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionSignature {
    params: Vec<RxType>,
    return_type: RxType,
}

impl FunctionSignature {
    pub fn new(params: Vec<RxType>, return_type: RxType) -> Self {
        Self {
            params,
            return_type,
        }
    }

    pub fn params(&self) -> &Vec<RxType> {
        &self.params
    }

    pub fn return_type(&self) -> &RxType {
        &self.return_type
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct MethodSignature {
    params: Vec<RxType>,
    return_type: RxType,
    pub self_kind: SelfKind,
}

impl MethodSignature {
    pub fn new(params: Vec<RxType>, return_type: RxType, self_kind: SelfKind) -> Self {
        Self {
            params,
            return_type,
            self_kind,
        }
    }

    pub fn params(&self) -> &Vec<RxType> {
        &self.params
    }

    pub fn return_type(&self) -> &RxType {
        &self.return_type
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructLayout {
    pub name: String,
    pub fields: Vec<StructFieldLayout>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructFieldLayout {
    pub name: String,
    pub ty: RxType,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArrayLayout {
    pub elem_type: RxType,
    pub size: Option<usize>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StaticMethodRef {
    pub type_name: String,
    pub method_name: String,
}

#[derive(Debug, Clone, Default)]
pub struct TypeContext {
    node_types: HashMap<NodeId, RxType>,
    node_symbols: HashMap<NodeId, Symbol>,
    node_const: HashMap<NodeId, RxValue>,
    const_items: HashMap<String, (RxType, RxValue)>,
    functions: HashMap<String, FunctionSignature>,
    methods: HashMap<(String, String), MethodSignature>,
    static_methods: HashMap<(String, String), FunctionSignature>,
    static_method_refs: HashMap<NodeId, StaticMethodRef>,
    struct_layouts: HashMap<String, StructLayout>,
    array_layouts: HashMap<NodeId, ArrayLayout>,
    next_id: NodeId,
}

impl TypeContext {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn assign_node_id(&mut self) -> NodeId {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    pub fn set_type(&mut self, node_id: NodeId, ty: RxType) {
        self.node_types.insert(node_id, ty);
    }

    pub fn get_type(&self, node_id: NodeId) -> Option<&RxType> {
        self.node_types.get(&node_id)
    }

    pub fn set_symbol(&mut self, node_id: NodeId, symbol: Symbol) {
        self.node_symbols.insert(node_id, symbol);
    }

    pub fn get_symbol(&self, node_id: NodeId) -> Option<&Symbol> {
        self.node_symbols.get(&node_id)
    }

    pub fn set_const_item(&mut self, name: impl Into<String>, ty: RxType, value: RxValue) {
        self.const_items.insert(name.into(), (ty, value));
    }

    pub fn get_const_value(&self, name: &str) -> Option<&(RxType, RxValue)> {
        self.const_items.get(name)
    }

    pub fn set_func_sig(
        &mut self,
        name: impl Into<String>,
        params: Vec<RxType>,
        return_type: RxType,
    ) {
        let name = name.into();
        self.functions
            .insert(name, FunctionSignature::new(params, return_type));
    }

    pub fn get_function(&self, name: &str) -> Option<&FunctionSignature> {
        self.functions.get(name)
    }

    pub fn set_method_sig(
        &mut self,
        type_name: impl Into<String>,
        method_name: impl Into<String>,
        params: Vec<RxType>,
        return_type: RxType,
        self_kind: SelfKind,
    ) {
        let key = (type_name.into(), method_name.into());
        self.methods
            .insert(key, MethodSignature::new(params, return_type, self_kind));
    }

    pub fn get_method(&self, type_name: &str, method_name: &str) -> Option<&MethodSignature> {
        self.methods
            .get(&(type_name.to_string(), method_name.to_string()))
    }

    pub fn set_static_method_sig(
        &mut self,
        type_name: impl Into<String>,
        method_name: impl Into<String>,
        params: Vec<RxType>,
        return_type: RxType,
    ) {
        let key = (type_name.into(), method_name.into());
        self.static_methods
            .insert(key, FunctionSignature::new(params, return_type));
    }

    pub fn set_static_method_ref(
        &mut self,
        node_id: NodeId,
        type_name: impl Into<String>,
        method_name: impl Into<String>,
    ) {
        let type_name = type_name.into();
        let method_name = method_name.into();
        self.static_method_refs.insert(
            node_id,
            StaticMethodRef {
                type_name,
                method_name,
            },
        );
    }

    pub fn get_static_method_ref(&self, node_id: NodeId) -> Option<&StaticMethodRef> {
        self.static_method_refs.get(&node_id)
    }

    pub fn get_static_method(
        &self,
        type_name: &str,
        method_name: &str,
    ) -> Option<&FunctionSignature> {
        self.static_methods
            .get(&(type_name.to_string(), method_name.to_string()))
    }

    pub fn set_struct_layout(&mut self, name: impl Into<String>, fields: Vec<(String, RxType)>) {
        let name = name.into();
        let layout = StructLayout {
            name: name.clone(),
            fields: fields
                .into_iter()
                .map(|(name, ty)| StructFieldLayout { name, ty })
                .collect(),
        };
        self.struct_layouts.insert(name, layout);
    }

    pub fn get_struct_layout(&self, name: &str) -> Option<&StructLayout> {
        self.struct_layouts.get(name)
    }

    pub fn set_array_layout(&mut self, node_id: NodeId, elem_type: RxType, size: Option<usize>) {
        let layout = ArrayLayout { elem_type, size };
        self.array_layouts.insert(node_id, layout);
    }

    pub fn get_array_layout(&self, node_id: NodeId) -> Option<&ArrayLayout> {
        self.array_layouts.get(&node_id)
    }
}
