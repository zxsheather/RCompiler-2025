use crate::frontend::lexer::TokenType::Integer;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("Lexical error at position {position}: {message}")]
pub struct LexError {
    pub message: String,
    pub position: usize,
}

pub type LexResult<T> = Result<T, LexError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenType {
    // Literals
    Integer(i32),
    Unit,

    // Keywords
    Let,
    If,
    Else,
    While,
    Loop,
    Bool,
    True,
    False,
    Fn,
    I32,

    // Identifiers
    Identifier(String),

    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Assign,
    Equal,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    NotEqual,
    Arrow,
    Colon,

    // Delimiters
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Semicolon,
    Comma,

    // Special
    Eof,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Default for Span {
    fn default() -> Self {
        Self { start: 0, end: 0 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub ty: TokenType,
    pub span: Span,
}

pub struct Lexer<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    pub fn tokenize(&mut self) -> LexResult<Vec<Token>> {
        let mut tokens = Vec::new();
        Ok(tokens)
    }

    pub fn next_token(&mut self) -> LexResult<Token> {
        Ok(Token{ty: Integer(0), span: Span::default()})
    }

    pub fn is_end(&self) -> bool {
        return true;
    }

    pub fn advance(&mut self) {

    }

    pub fn current_char(&self) -> char {
        '\0'
    }

    pub fn peek(&self) -> char {
        '\0'
    }
}
