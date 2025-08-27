use thiserror::Error;

use crate::frontend::{
    r_lexer::{error, token::TokenType},
    r_semantic::types::RxType,
};

pub type SemanticResult<T> = Result<T, SemanticError>;

#[derive(Error, Debug, Clone, PartialEq)]
pub enum SemanticError {
    #[error("Undefined identifier '{name}' at line {line}, column {column}")]
    UndefinedIdentifier {
        name: String,
        line: usize,
        column: usize,
    },

    #[error("Attempt to assign to immutable variable '{name}' at line {line}, column {column}")]
    AssignImmutableVar {
        name: String,
        line: usize,
        column: usize,
    },

    #[error(
        "Type mismatch in assignment, expected {expected}, found {found} at line {line}, column {column}"
    )]
    AssignTypeMismatched {
        expected: RxType,
        found: RxType,
        line: usize,
        column: usize,
    },

    #[error(
        "Invalid index type: expected integer, found '{found}' at line {line}, column {column}"
    )]
    InvalidIndexType {
        found: RxType,
        line: usize,
        column: usize,
    },

    #[error("Indexing non-array value typed {found}, at line {line}, column {column}")]
    IndexNonArray {
        found: RxType,
        line: usize,
        column: usize,
    },

    #[error("Unknown callee '{name}' at line {line}, column {column}")]
    UnknownCallee {
        name: String,
        line: usize,
        column: usize,
    },

    #[error(
        "Arity mismatch in call to '{operator}': expected '{expected_type}', found '{found}' at line {line}, column {column}"
    )]
    ArityMismatch {
        operator: String,
        expected_type: String,
        found: RxType,
        line: usize,
        column: usize,
    },

    #[error(
        "Function '{callee}' expected {expected} args, found {found} args, at line {line}, column {column}"
    )]
    ArgsNumMismatched {
        callee: String,
        expected: usize,
        found: usize,
        line: usize,
        column: usize,
    },

    #[error(
        "Argument {index} of '{callee}' expected '{expected}' but got '{found}', at line {line}, column {column}"
    )]
    ArgTypeMismatched {
        callee: String,
        index: usize,
        expected: RxType,
        found: RxType,
        line: usize,
        column: usize,
    },

    #[error("Redeclaration of function '{name}', at line {line}, column {column}")]
    FunctionRedeclaration {
        name: String,
        line: usize,
        column: usize,
    },

    #[error(
        "Function '{name}' return type mismatch: expected {expected}, found {found} at line {line}, column {column}"
    )]
    FunctionReturnTypeMismatch {
        name: String,
        expected: RxType,
        found: RxType,
        line: usize,
        column: usize,
    },

    #[error("Identifier '{name}' need annotation at line {line}, column {column}")]
    NeedAnnotation {
        name: String,
        line: usize,
        column: usize,
    },

    #[error("Unknown type of variable '{name}' at line {line}, column {column}")]
    UnknownType {
        name: String,
        line: usize,
        column: usize,
    },

    #[error("Declaration of variable '{name}' out of scope at line {line}, column {column}")]
    DeclarationOutOfScope {
        name: String,
        line: usize,
        column: usize,
    },

    #[error("Mixed typed array containing {type1} and {type2}")]
    MixedTypedArray { type1: RxType, type2: RxType },

    #[error("Invalid unary operand type, expected '{expected_type}', found '{found_type}'")]
    InvalidUnaryOperandType {
        expected_type: String,
        found_type: String,
        line: usize,
        column: usize,
    },

    #[error(
        "Unsupported unary operation '{op}' for type '{type_}' at line {line}, column {column}"
    )]
    UnsupportedUnaryOperation {
        op: String,
        type_: String,
        line: usize,
        column: usize,
    },

    #[error(
        "Two operand type mismatched for '{op}', left '{left}', right '{right}', at line {line}, column {column}"
    )]
    MismatchedBinaryTypes {
        op: String,
        left: RxType,
        right: RxType,
        line: usize,
        column: usize,
    },

    #[error(
        "Logical operators require bools, found left '{left}', right '{right}', at line {line}, column {column}"
    )]
    InvalidLogicalTypes {
        left: RxType,
        right: RxType,
        line: usize,
        column: usize,
    },

    #[error(
        "Left-hand side of '=' must be an identifier/array[index]/struct.field, at line {line}, column {column}"
    )]
    InvalidLValueType { line: usize, column: usize },

    #[error("{msg}, at line {line}, column {column}")]
    Generic {
        msg: String,
        line: usize,
        column: usize,
    },

    #[error("Condition must be boolean, found {found}, at line {line}, column {column}")]
    InvalidConditionType {
        found: RxType,
        line: usize,
        column: usize,
    },

    #[error(
        "Mismatched branch types in if expression, then type '{then_ty}', else type '{else_ty}', at line {line}, column {column}"
    )]
    BranchTypeMismatched {
        then_ty: RxType,
        else_ty: RxType,
        line: usize,
        column: usize,
    },

    #[error("Unknown struct '{name}' at line {line}, column {column}")]
    UnknownStruct {
        name: String,
        line: usize,
        column: usize,
    },

    #[error("Struct '{name}' field '{field}' not found at line {line}, column {column}")]
    UnknownStructField {
        name: String,
        field: String,
        line: usize,
        column: usize,
    },

    #[error(
        "Struct literal '{name}' field '{field}' type mismatch: expected {expected}, found {found}, at line {line}, column {column}"
    )]
    StructFieldTypeMismatch {
        name: String,
        field: String,
        expected: RxType,
        found: RxType,
        line: usize,
        column: usize,
    },

    #[error("Unknown trait '{name}' at line {line}, column {column}")]
    UnknownTrait {
        name: String,
        line: usize,
        column: usize,
    },

    #[error(
        "Method '{method}' in impl of trait '{trait_name}' for type '{type_name}' not found in trait at line {line}, column {column}"
    )]
    ImplMethodNotInTrait {
        trait_name: String,
        type_name: String,
        method: String,
        line: usize,
        column: usize,
    },

    #[error(
        "Impl of trait '{trait_name}' for type '{type_name}' is missing method '{method}' at line {line}, column {column}"
    )]
    MissingTraitImplMethod {
        trait_name: String,
        type_name: String,
        method: String,
        line: usize,
        column: usize,
    },

    #[error(
        "Signature mismatch for method '{method}' in impl of trait '{trait_name}' for type '{type_name}': {detail} at line {line}, column {column}"
    )]
    TraitMethodSignatureMismatch {
        trait_name: String,
        type_name: String,
        method: String,
        detail: String,
        line: usize,
        column: usize,
    },

    #[error(
        "Duplicated trait implementation for '{trait_name}' on type '{type_name}' at line {line}, column {column}"
    )]
    DuplicatedTraitImpl {
        trait_name: String,
        type_name: String,
        line: usize,
        column: usize,
    },

    #[error(
        "Cannot take mutable reference to immutable value '{name}' at line {line}, column {column}"
    )]
    BorrowMutFromImmutable {
        name: String,
        line: usize,
        column: usize,
    },

    #[error("Type mismatch: expected {expected}, found {found}, at line {line}, column {column}")]
    TypeMismatch {
        expected: RxType,
        found: RxType,
        line: usize,
        column: usize,
    },
}
