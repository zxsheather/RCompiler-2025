use thiserror::Error;

pub type ParseResult<T> = Result<T, ParseError>;

#[derive(Error, Debug, Clone, PartialEq)]
pub enum ParseError {
    #[error("Parser error at line {line}, column {column}: {message}")]
    Generic {
        message: String,
        line: usize,
        column: usize,
    },
}
