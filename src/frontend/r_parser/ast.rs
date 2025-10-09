use crate::frontend::{r_lexer::token::Token, r_semantic::tyctxt::NodeId};
use serde::{Serialize, de};

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum AstNode {
    Function(FunctionNode),
    Statement(StatementNode),
    Expression(ExpressionNode),
    Struct(StructDeclNode),
    Enum(EnumDeclNode),
    Impl(ImplNode),
    Trait(TraitDeclNode),
    ImplTrait(ImplTraitBlockNode),
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum TypeNode {
    I32(Token),
    U32(Token),
    ISize(Token),
    USize(Token),
    Bool(Token),
    String(Token),
    Str(Token),
    Char(Token),
    Unit,
    Tuple(Vec<TypeNode>),
    Named(Token),
    Array {
        elem_type: Box<TypeNode>,
        size: Option<Box<ExpressionNode>>,
    },
    Ref {
        inner_type: Box<TypeNode>,
        mutable: bool,
    },
    SelfRef {
        mutable: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct FunctionNode {
    pub node_id: NodeId,
    pub fn_token: Token,
    pub name: Token,
    pub param_list: ParamListNode,
    pub return_type: Option<TypeNode>,
    pub body: BlockNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ParamListNode {
    pub node_id: NodeId,
    pub params: Vec<ParamNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ParamNode {
    pub node_id: NodeId,
    pub name: Token,
    pub type_annotation: Option<TypeNode>,
    pub mutable: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct BlockNode {
    pub node_id: NodeId,
    pub stats: Vec<StatementNode>,
    pub final_expr: Option<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct StructDeclNode {
    pub node_id: NodeId,
    pub struct_token: Token,
    pub name: Token,
    pub fields: Vec<StructFieldNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ImplNode {
    pub node_id: NodeId,
    pub impl_token: Token,
    pub name: Token,
    pub methods: Vec<FunctionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TraitDeclNode {
    pub node_id: NodeId,
    pub trait_token: Token,
    pub name: Token,
    pub methods: Vec<TraitMethodSigNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TraitMethodSigNode {
    pub node_id: NodeId,
    pub fn_token: Token,
    pub name: Token,
    pub param_list: ParamListNode,
    pub return_type: Option<TypeNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ImplTraitBlockNode {
    pub node_id: NodeId,
    pub impl_token: Token,
    pub trait_name: Token,
    pub for_token: Token,
    pub type_name: Token,
    pub methods: Vec<FunctionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct StructFieldNode {
    pub node_id: NodeId,
    pub name: Token,
    pub type_annotation: TypeNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct EnumDeclNode {
    pub node_id: NodeId,
    pub enum_token: Token,
    pub name: Token,
    pub variants: Vec<EnumVariantNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct EnumVariantNode {
    pub node_id: NodeId,
    pub name: Token,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum ArrayLiteralNode {
    Elements {
        node_id: NodeId,
        elements: Vec<ExpressionNode>,
    },
    Repeated {
        node_id: NodeId,
        element: Box<ExpressionNode>,
        size: Box<ExpressionNode>,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TupleLiteralNode {
    pub node_id: NodeId,
    pub elements: Vec<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct StructLiteralNode {
    pub node_id: NodeId,
    pub name: Token,
    pub fields: Vec<StructLiteralFieldNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct StructLiteralFieldNode {
    pub node_id: NodeId,
    pub name: Token,
    pub value: ExpressionNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ConstItemNode {
    pub node_id: NodeId,
    pub const_token: Token,
    pub name: Token,
    pub type_annotation: TypeNode,
    pub value: ExpressionNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum StatementNode {
    Let(LetStatementNode),
    Assign(AssignStatementNode),
    Expression(ExprStatementNode),
    Block(BlockNode),
    Const(ConstItemNode),
    Func(FunctionNode),
    Struct(StructDeclNode),
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct LetStatementNode {
    pub node_id: NodeId,
    pub let_token: Token,
    pub mutable: bool,
    pub identifier: Token,
    pub type_annotation: Option<TypeNode>,
    pub value: Option<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct AssignStatementNode {
    pub node_id: NodeId,
    pub identifier: Token,
    pub value: ExpressionNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ExprStatementNode {
    pub node_id: NodeId,
    pub expression: ExpressionNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum ExpressionNode {
    // Primaries
    Identifier(Token, NodeId),
    IntegerLiteral(Token, NodeId),
    StringLiteral(Token, NodeId),
    BoolLiteral(Token, NodeId),
    CharLiteral(Token, NodeId),
    Underscore(Token, NodeId),
    Block(Box<BlockNode>),
    TupleLiteral(TupleLiteralNode),
    ArrayLiteral(ArrayLiteralNode),
    StructLiteral(StructLiteralNode),
    StaticMember(StaticMemberExprNode),
    // Complex
    Unary(UnaryExprNode),
    Binary(BinaryExprNode),
    Call(CallExprNode),
    MethodCall(MethodCallExprNode),
    Index(IndexExprNode),
    If(Box<IfExprNode>),
    While(Box<WhileExprNode>),
    Loop(Box<LoopExprNode>),
    Member(MemberExprNode),
    Ref(RefExprNode),
    Deref(DerefExprNode),
    Return(Box<ReturnExprNode>),
    Break(Box<BreakExprNode>),
    Continue(Box<ContinueExprNode>),
    As(Box<AsExprNode>),
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct UnaryExprNode {
    pub node_id: NodeId,
    pub operator: Token,
    pub operand: Box<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct BinaryExprNode {
    pub node_id: NodeId,
    pub left_operand: Box<ExpressionNode>,
    pub operator: Token,
    pub right_operand: Box<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IndexExprNode {
    pub node_id: NodeId,
    pub array: Box<ExpressionNode>,
    pub index: Box<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CallExprNode {
    pub node_id: NodeId,
    pub function: Box<ExpressionNode>,
    pub args: Vec<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IfExprNode {
    pub node_id: NodeId,
    pub if_token: Token,
    pub condition: ExpressionNode,
    pub then_block: BlockNode,
    pub else_block: Option<ElseBodyNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum ElseBodyNode {
    Block(Box<BlockNode>),
    If(Box<IfExprNode>),
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct WhileExprNode {
    pub node_id: NodeId,
    pub while_token: Token,
    pub condition: ExpressionNode,
    pub body: BlockNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MemberExprNode {
    pub node_id: NodeId,
    pub object: Box<ExpressionNode>,
    pub field: Token,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct StaticMemberExprNode {
    pub node_id: NodeId,
    pub type_name: Token,
    pub member: Token,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct RefExprNode {
    pub ref_token: Token,
    pub node_id: NodeId,
    pub mutable: bool,
    pub operand: Box<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MethodCallExprNode {
    pub node_id: NodeId,
    pub object: Box<ExpressionNode>,
    pub method: Token,
    pub args: Vec<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ReturnExprNode {
    pub node_id: NodeId,
    pub return_token: Token,
    pub value: Option<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct LoopExprNode {
    pub node_id: NodeId,
    pub loop_token: Token,
    pub body: BlockNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct BreakExprNode {
    pub node_id: NodeId,
    pub break_token: Token,
    pub value: Option<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ContinueExprNode {
    pub node_id: NodeId,
    pub continue_token: Token,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct AsExprNode {
    pub node_id: NodeId,
    pub expr: Box<ExpressionNode>,
    pub as_token: Token,
    pub type_name: TypeNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct DerefExprNode {
    pub node_id: NodeId,
    pub star_token: Token,
    pub operand: Box<ExpressionNode>,
}
