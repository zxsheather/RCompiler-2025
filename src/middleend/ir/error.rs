use crate::{frontend::r_semantic::tyctxt::NodeId, middleend::ir::module::IRType};
use thiserror::Error;

pub type LowerResult<T> = Result<T, LowerError>;

#[derive(Debug, Error)]
pub enum LowerError {
    #[error("missing type information for node {0}")]
    MissingType(NodeId),
    #[error("missing type for binding '{0}'")]
    MissingBindingType(String),
    #[error("missing type annotation for parameter '{0}'")]
    MissingParameterType(String),
    #[error("unsupported expression: {0}")]
    UnsupportedExpression(String),
    #[error("undefined identifier '{0}'")]
    UndefinedIdentifier(String),
    #[error("immutable binding '{0}' cannot be assigned")]
    ImmutableBinding(String),
    #[error("expected value when returning from function '{0}'")]
    MissingReturnValue(String),
    #[error("failed to parse integer literal '{0}'")]
    IntegerLiteral(String),
    #[error("unsupported cast : '{0}'")]
    UnsupportedCast(String),
    #[error("type mismatch: expected '{expected:?}', found '{found:?}'")]
    TypeMismatch { expected: IRType, found: IRType },
}
