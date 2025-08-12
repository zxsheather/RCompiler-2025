use crate::frontend::r_lexer::token::Token;
use serde::Serialize;

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum AstNode {
    Function(FunctionNode),
    Statement(StatementNode),
    Expression(ExpressionNode),
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum TypeNode {
    I32(Token),
    U32(Token),
    ISize(Token),
    USize(Token),
    Bool(Token),
    String(Token),
    Unit,
    Tuple(Vec<TypeNode>),
    Array {
        elem_type: Box<TypeNode>,
        size: Option<Token>,
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
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct BlockNode {
    pub stats: Vec<StatementNode>,
    pub final_expr: Option<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ArrayLiteralNode {
    pub elements: Vec<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TupleLiteralNode {
    pub elements: Vec<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum StatementNode {
    Let(LetStatementNode),
    Assign(AssignStatementNode),
    Expression(ExprStatementNode),
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
    Block(Box<BlockNode>),
    TupleLiteral(TupleLiteralNode),
    ArrayLiteral(ArrayLiteralNode),
    // Complex
    Unary(UnaryExprNode),
    Binary(BinaryExprNode),
    Call(CallExprNode),
    Index(IndexExprNode),
    If(Box<IfExprNode>),
    While(Box<WhileExprNode>),
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
