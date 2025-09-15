use crate::frontend::r_lexer::token::Token;
use serde::{Serialize, de};

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum AstNode {
    Function(FunctionNode),
    Statement(StatementNode),
    Expression(ExpressionNode),
    Struct(StructDeclNode),
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
    pub fn_token: Token,
    pub name: Token,
    pub param_list: ParamListNode,
    pub return_type: Option<TypeNode>,
    pub body: BlockNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ParamListNode {
    pub params: Vec<ParamNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ParamNode {
    pub name: Token,
    pub type_annotation: Option<TypeNode>,
    pub mutable: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct BlockNode {
    pub stats: Vec<StatementNode>,
    pub final_expr: Option<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct StructDeclNode {
    pub struct_token: Token,
    pub name: Token,
    pub fields: Vec<StructFieldNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ImplNode {
    pub impl_token: Token,
    pub name: Token,
    pub methods: Vec<FunctionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TraitDeclNode {
    pub trait_token: Token,
    pub name: Token,
    pub methods: Vec<TraitMethodSigNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TraitMethodSigNode {
    pub fn_token: Token,
    pub name: Token,
    pub param_list: ParamListNode,
    pub return_type: Option<TypeNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ImplTraitBlockNode {
    pub impl_token: Token,
    pub trait_name: Token,
    pub for_token: Token,
    pub type_name: Token,
    pub methods: Vec<FunctionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct StructFieldNode {
    pub name: Token,
    pub type_annotation: TypeNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum ArrayLiteralNode {
    Elements {
        elements: Vec<ExpressionNode>,
    },
    Repeated {
        element: Box<ExpressionNode>,
        size: Box<ExpressionNode>,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TupleLiteralNode {
    pub elements: Vec<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct StructLiteralNode {
    pub name: Token,
    pub fields: Vec<StructLiteralFieldNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct StructLiteralFieldNode {
    pub name: Token,
    pub value: ExpressionNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ConstItemNode {
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
    Const(ConstItemNode),
    Func(FunctionNode),
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct LetStatementNode {
    pub let_token: Token,
    pub mutable: bool,
    pub identifier: Token,
    pub type_annotation: Option<TypeNode>,
    pub value: ExpressionNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct AssignStatementNode {
    pub identifier: Token,
    pub value: ExpressionNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ExprStatementNode {
    pub expression: ExpressionNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum ExpressionNode {
    // Primaries
    Identifier(Token),
    IntegerLiteral(Token),
    StringLiteral(Token),
    BoolLiteral(Token),
    CharLiteral(Token),
    Underscore(Token),
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
    pub operator: Token,
    pub operand: Box<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct BinaryExprNode {
    pub left_operand: Box<ExpressionNode>,
    pub operator: Token,
    pub right_operand: Box<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IndexExprNode {
    pub array: Box<ExpressionNode>,
    pub index: Box<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CallExprNode {
    pub function: Box<ExpressionNode>,
    pub args: Vec<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct IfExprNode {
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
    pub while_token: Token,
    pub condition: ExpressionNode,
    pub body: BlockNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MemberExprNode {
    pub object: Box<ExpressionNode>,
    pub field: Token,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct StaticMemberExprNode {
    pub type_name: Token,
    pub member: Token,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct RefExprNode {
    pub mutable: bool,
    pub operand: Box<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MethodCallExprNode {
    pub object: Box<ExpressionNode>,
    pub method: Token,
    pub args: Vec<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ReturnExprNode {
    pub return_token: Token,
    pub value: Option<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct LoopExprNode {
    pub loop_token: Token,
    pub body: BlockNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct BreakExprNode {
    pub break_token: Token,
    pub value: Option<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ContinueExprNode {
    pub continue_token: Token,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct AsExprNode {
    pub expr: Box<ExpressionNode>,
    pub as_token: Token,
    pub type_name: TypeNode,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct DerefExprNode {
    pub star_token: Token,
    pub operand: Box<ExpressionNode>,
}
