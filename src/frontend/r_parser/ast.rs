use crate::frontend::r_lexer::token::Token;

#[derive(Debug, Clone, PartialEq)]
pub enum AstNode {
    Function(FunctionNode),
    Statement(StatementNode),
    Expression(ExpressionNode),
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeNode {
    I32(Token),
    U32(Token),
    ISize(Token),
    USize(Token),
    F32(Token),
    F64(Token),
    Bool(Token),
    String(Token),
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionNode {
    pub fn_token: Token,
    pub name: Token,
    pub param_list: ParamListNode,
    pub return_type: Option<TypeNode>,
    pub body: BlockNode,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParamListNode {
    pub params: Vec<ParamNode>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParamNode {
    pub name: Token,
    pub type_annotation: Option<TypeNode>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockNode {
    pub stats: Vec<StatementNode>,
    pub final_expr: Option<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementNode {
    Let(LetStatementNode),
    Assign(AssignStatementNode),
    Expression(ExprStatementNode),
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetStatementNode {
    pub let_token: Token,
    pub identifier: Token,
    pub type_annotation: Option<TypeNode>,
    pub value: ExpressionNode,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AssignStatementNode {
    pub identifier: Token,
    pub value: ExpressionNode,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExprStatementNode {
    pub expression: ExpressionNode,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExpressionNode {
    // Primaries
    Identifier(Token),
    IntegerLiteral(Token),
    FloatLiteral(Token),
    StringLiteral(Token),
    BoolLiteral(Token),
    Block(Box<BlockNode>),
    // Complex
    Unary(UnaryExprNode),
    Binary(BinaryExprNode),
    Call(CallExprNode),
    If(Box<IfExprNode>),
    While(Box<WhileExprNode>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnaryExprNode {
    pub operator: Token,
    pub operand: Box<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExprNode {
    pub left_operand: Box<ExpressionNode>,
    pub operator: Token,
    pub right_operand: Box<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExprNode {
    pub function: Box<ExpressionNode>,
    pub args: Vec<ExpressionNode>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfExprNode {
    pub if_token: Token,
    pub condition: ExpressionNode,
    pub then_block: BlockNode,
    pub else_block: Option<ElseBodyNode>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ElseBodyNode {
    Block(Box<BlockNode>),
    If(Box<IfExprNode>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileExprNode {
    pub while_token: Token,
    pub condition: ExpressionNode,
    pub body: BlockNode,
}
