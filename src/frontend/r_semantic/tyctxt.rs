use std::collections::HashMap;

use crate::frontend::r_semantic::{
    analyzer::Symbol,
    types::{RxType, RxValue},
};

pub type NodeId = usize;

#[derive(Debug, Clone, Default)]
pub struct TypeContext {
    node_types: HashMap<NodeId, RxType>,
    node_symbols: HashMap<NodeId, Symbol>,
    node_const: HashMap<NodeId, RxValue>,
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
}
