use serde::Serialize;
use std::fmt;

/// Position information for tokens
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Default)]
pub struct Position {
    pub line: usize,
    pub column: usize,
    pub index: usize,
}

impl Position {
    pub fn new(line: usize, column: usize, index: usize) -> Self {
        Self {
            line,
            column,
            index,
        }
    }

    pub fn start() -> Self {
        Self::new(1, 1, 0)
    }
}

/// Represents a token with its type, lexeme, and position
#[derive(Debug, Clone, PartialEq, Serialize, Default)]
pub struct Token {
    pub token_type: TokenType,
    pub lexeme: String,
    pub position: Position,
}

/// All possible token types in the Rust-like language
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Default)]
pub enum TokenType {
    // Keywords - Reserved words
    As,
    Break,
    Const,
    Continue,
    Crate,
    Else,
    Enum,
    Extern,
    False,
    Fn,
    For,
    If,
    Impl,
    In,
    Let,
    Loop,
    Match,
    Mod,
    Move,
    Mut,
    Pub,
    Ref,
    Return,
    SelfLower, // self
    SelfUpper, // Self
    Static,
    Struct,
    Super,
    Trait,
    True,
    Type,
    Unsafe,
    Use,
    Where,
    While,
    Async,
    Await,
    Dyn,
    I32,
    U32,
    ISize,
    USize,
    Bool,
    StringType,
    StrType,
    CharType,

    // Reserved keywords for future use
    Abstract,
    Become,
    Box,
    Do,
    Final,
    Macro,
    Override,
    Priv,
    Typeof,
    Unsized,
    Virtual,
    Yield,
    Try,

    // Identifiers and literals
    Identifier,
    IntegerLiteral,
    CharLiteral,
    ByteLiteral,
    StringLiteral,
    RawStringLiteral,
    ByteStringLiteral,
    RawByteStringLiteral,
    CStringLiteral,
    RawCStringLiteral,

    // Multi-character operators
    DotDotDot,  // ...
    DotDotEq,   // ..=
    SLEq,       // <<=
    SREq,       // >>=
    LEq,        // <=
    EqEq,       // ==
    NEq,        // !=
    GEq,        // >=
    AndAnd,     // &&
    OrOr,       // ||
    SL,         // <<
    SR,         // >>
    PlusEq,     // +=
    MinusEq,    // -=
    MulEq,      // *=
    DivEq,      // /=
    ModEq,      // %=
    XorEq,      // ^=
    AndEq,      // &=
    OrEq,       // |=
    DotDot,     // ..
    ColonColon, // ::
    RArrow,     // ->
    LArrow,     // <-
    FatArrow,   // =>

    // Single-character operators and punctuation
    Eq,         // =
    Lt,         // <
    Gt,         // >
    Not,        // !
    Tilde,      // ~
    Plus,       // +
    Minus,      // -
    Mul,        // *
    Div,        // /
    Percent,    // %
    Xor,        // ^
    And,        // &
    Or,         // |
    At,         // @
    Dot,        // .
    Comma,      // ,
    Semicolon,  // ;
    Colon,      // :
    Pound,      // #
    Dollar,     // $
    Question,   // ?
    Underscore, // _

    // Delimiters
    LBrace,   // {
    RBrace,   // }
    LBracket, // [
    RBracket, // ]
    LParen,   // (
    RParen,   // )

    // Special tokens
    Eof,
    #[default]
    None,
}

impl TokenType {
    /// Returns the string representation of the token type
    pub fn as_str(&self) -> &'static str {
        match self {
            TokenType::As => "as",
            TokenType::Break => "break",
            TokenType::Const => "const",
            TokenType::Continue => "continue",
            TokenType::Crate => "crate",
            TokenType::Else => "else",
            TokenType::Enum => "enum",
            TokenType::Extern => "extern",
            TokenType::False => "false",
            TokenType::Fn => "fn",
            TokenType::For => "for",
            TokenType::If => "if",
            TokenType::Impl => "impl",
            TokenType::In => "in",
            TokenType::Let => "let",
            TokenType::Loop => "loop",
            TokenType::Match => "match",
            TokenType::Mod => "mod",
            TokenType::Move => "move",
            TokenType::Mut => "mut",
            TokenType::Pub => "pub",
            TokenType::Ref => "ref",
            TokenType::Return => "return",
            TokenType::SelfLower => "self",
            TokenType::SelfUpper => "Self",
            TokenType::Static => "static",
            TokenType::Struct => "struct",
            TokenType::Super => "super",
            TokenType::Trait => "trait",
            TokenType::True => "true",
            TokenType::Type => "type",
            TokenType::Unsafe => "unsafe",
            TokenType::Use => "use",
            TokenType::Where => "where",
            TokenType::While => "while",
            TokenType::Async => "async",
            TokenType::Await => "await",
            TokenType::Dyn => "dyn",
            TokenType::Abstract => "abstract",
            TokenType::Become => "become",
            TokenType::Box => "box",
            TokenType::Do => "do",
            TokenType::Final => "final",
            TokenType::Macro => "macro",
            TokenType::Override => "override",
            TokenType::Priv => "priv",
            TokenType::Typeof => "typeof",
            TokenType::Unsized => "unsized",
            TokenType::Virtual => "virtual",
            TokenType::Yield => "yield",
            TokenType::Try => "try",
            TokenType::I32 => "i32",
            TokenType::U32 => "u32",
            TokenType::ISize => "isize",
            TokenType::USize => "usize",
            TokenType::Bool => "bool",
            TokenType::StringType => "String",
            TokenType::StrType => "str",
            TokenType::StringLiteral => "string",
            TokenType::CharLiteral => "char_literal",
            TokenType::CharType => "char",

            TokenType::DotDotDot => "...",
            TokenType::DotDotEq => "..=",
            TokenType::SLEq => "<=",
            TokenType::SREq => ">>=",
            TokenType::LEq => "<=",
            TokenType::EqEq => "==",
            TokenType::NEq => "!=",
            TokenType::GEq => ">=",
            TokenType::AndAnd => "&&",
            TokenType::OrOr => "||",
            TokenType::SL => "<<",
            TokenType::SR => ">>",
            TokenType::PlusEq => "+=",
            TokenType::MinusEq => "-=",
            TokenType::MulEq => "*=",
            TokenType::DivEq => "/=",
            TokenType::ModEq => "%=",
            TokenType::XorEq => "^=",
            TokenType::AndEq => "&=",
            TokenType::OrEq => "|=",
            TokenType::ColonColon => "::",
            TokenType::RArrow => "->",
            TokenType::LArrow => "<-",
            TokenType::FatArrow => "=>",

            TokenType::Eq => "=",
            TokenType::Lt => "<",
            TokenType::Gt => ">",
            TokenType::Not => "!",
            TokenType::Tilde => "~",
            TokenType::Plus => "+",
            TokenType::Minus => "-",
            TokenType::Mul => "*",
            TokenType::Div => "/",
            TokenType::Percent => "%",
            TokenType::Xor => "^",
            TokenType::And => "&",
            TokenType::Or => "|",
            TokenType::At => "@",
            TokenType::Dot => ".",
            TokenType::Comma => ",",
            TokenType::Semicolon => ";",
            TokenType::Colon => ":",
            TokenType::Pound => "#",
            TokenType::Dollar => "$",
            TokenType::Question => "?",
            TokenType::Underscore => "_",

            TokenType::LBrace => "{",
            TokenType::RBrace => "}",
            TokenType::LBracket => "[",
            TokenType::RBracket => "]",
            TokenType::LParen => "(",
            TokenType::RParen => ")",

            TokenType::Eof => "EOF",
            _ => "",
        }
    }
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
