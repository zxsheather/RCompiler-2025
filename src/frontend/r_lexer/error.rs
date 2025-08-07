use thiserror::Error;

pub type LexResult<T> = Result<T, LexError>;

#[derive(Error, Debug, Clone, PartialEq)]
pub enum LexError {
    #[error("Invalid token at line {line}, column {column}: '{text}'")]
    InvalidToken {
        text: String,
        line: usize,
        column: usize,
    },

    #[error("Lexer error at line {line}, column {column}: {message}")]
    Generic {
        message: String,
        line: usize,
        column: usize,
    },
}
