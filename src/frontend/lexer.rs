use crate::frontend::lexer::TokenType::Integer;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("Lexical error at line {line}, column {column}: {message}")]
pub struct LexError {
    pub message: String,
    pub line: usize,
    pub column: usize,
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
    Not,
    LogicAnd,
    LogicOr,
    And,
    Or,

    // Delimiters
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,
    Semicolon,
    Comma,

    // Special
    Eof,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Position {
    pub index: usize,
    pub line: usize,
    pub column: usize,
}

impl Default for Position {
    fn default() -> Self {
        Self {
            index: 0,
            line: 1,
            column: 1,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Span {
    pub fn new(start_pos: Position, end_pos: Position) -> Self {
        Self { start_pos, end_pos }
    }
}

impl Default for Span {
    fn default() -> Self {
        Self {
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub ty: TokenType,
    pub span: Span,
}

pub struct Lexer<'a> {
    input: &'a str,
    pos: Position,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            pos: Position::default(),
        }
    }

    pub fn tokenize(&mut self) -> LexResult<Vec<Token>> {
        let mut tokens = Vec::new();

        while !self.is_end() {
            self.skip_whitespace_and_comments()?;
            if !self.is_end() {
                tokens.push(self.next_token()?);
            }
        }

        Ok(tokens)
    }

    pub fn skip_whitespace_and_comments(&mut self) -> LexResult<()> {
        loop {
            if self.current_char().is_whitespace() {
                self.advance();
            } else if self.current_char() == '/' && self.peek() == '/' {
                self.lex_sin_line_comment()?;
            } else if self.current_char() == '/' && self.peek() == '*' {
                self.lex_mul_lines_comment()?;
            } else {
                break;
            }
        }
        Ok(())
    }

    pub fn lex_sin_line_comment(&mut self) -> LexResult<()> {
        self.advance();
        self.advance();
        while !self.is_end() && self.peek() != '\n' {
            self.advance();
        }
        self.advance(); 
        Ok(())
    }

    pub fn lex_mul_lines_comment(&mut self) -> LexResult<()> {
        let start_line = self.pos.line;
        let start_column = self.pos.column;
        self.advance();
        self.advance();

        let mut cnt = 1;
        while !self.is_end() && cnt > 0 {
            if self.current_char() == '/' && self.peek() == '*' {
                cnt += 1;
                self.advance();
                self.advance();
            } else if self.current_char() == '*' && self.peek() == '/' {
                cnt -= 1;
                self.advance();
                self.advance();
            } else {
                self.advance();
            }
        }

        if cnt > 0 {
            return Err(LexError {
                message: "Unterminated multi-line comment".to_string(),
                line: start_line,
                column: start_column,
            });
        }

        Ok(())
    }

    pub fn next_token(&mut self) -> LexResult<Token> {
        let mut span = Span::new(self.pos, self.pos);

        let res = match self.current_char() {
            '+' => Ok(Token {
                ty: TokenType::Plus,
                span,
            }),
            '-' => {
                let next_char = self.peek();
                if next_char == '>' {
                    self.advance();
                    span.end_pos = self.pos;
                    Ok(Token {
                        ty: TokenType::Arrow,
                        span,
                    })
                } else if next_char.is_numeric() {
                    self.lex_number()
                } else {
                    Ok(Token {
                        ty: TokenType::Minus,
                        span,
                    })
                }
            }
            '*' => Ok(Token {
                ty: TokenType::Star,
                span,
            }),
            '/' => Ok(Token {
                ty: TokenType::Slash,
                span,
            }),
            '%' => Ok(Token {
                ty: TokenType::Percent,
                span,
            }),
            ':' => Ok(Token {
                ty: TokenType::Colon,
                span,
            }),
            '=' => {
                let next_char = self.peek();
                if next_char == '=' {
                    self.advance();
                    span.end_pos = self.pos;
                    Ok(Token {
                        ty: TokenType::Equal,
                        span,
                    })
                } else {
                    Ok(Token {
                        ty: TokenType::Assign,
                        span,
                    })
                }
            },
            '!' => {
                let next_char = self.peek();
                if next_char == '=' {
                    self.advance();
                    span.end_pos = self.pos;
                    Ok(Token {
                        ty: TokenType::NotEqual,
                        span,
                    })
                } else {
                    Ok(Token {
                        ty: TokenType::Not,
                        span,
                    })
                }
            },
            '<' => {
                let next_char = self.peek();
                if next_char == '=' {
                    self.advance();
                    span.end_pos = self.pos;
                    Ok(Token {
                        ty: TokenType::LessEqual,
                        span,
                    })
                } else {
                    Ok(Token {
                        ty: TokenType::Less,
                        span,
                    })
                }
            },
            '>' => {
                let next_char = self.peek();
                if next_char == '=' {
                    self.advance();
                    span.end_pos = self.pos;
                    Ok(Token {
                        ty: TokenType::GreaterEqual,
                        span,
                    })
                } else {
                    Ok(Token {
                        ty: TokenType::Greater,
                        span,
                    })
                }
            },
            '(' => Ok(Token { ty: TokenType::LeftParen, span }),
            ')' => Ok(Token { ty: TokenType::RightParen, span }),
            '[' => Ok(Token { ty: TokenType::LeftBracket, span }),
            ']' => Ok(Token { ty: TokenType::RightBracket, span }),
            '{' => Ok(Token { ty: TokenType::LeftBrace, span }),
            '}' => Ok(Token { ty: TokenType::RightBrace, span }),
            ';' => Ok(Token { ty: TokenType::Semicolon, span }),
            ',' => Ok(Token { ty: TokenType::Comma, span }),
            '&' => {
                let next_char = self.peek();
                if next_char == '&' {
                    self.advance();
                    span.end_pos = self.pos;
                    Ok(Token {
                        ty: TokenType::LogicAnd,
                        span,
                    })
                } else {
                    Ok(Token {
                        ty: TokenType::And,
                        span,
                    })
                }
            },
            '|' => {
                let next_char = self.peek();
                if next_char == '|' {
                    self.advance();
                    span.end_pos = self.pos;
                    Ok(Token {
                        ty: TokenType::LogicOr,
                        span,
                    })
                } else {
                    Ok(Token {
                        ty: TokenType::Or,
                        span,
                    })
                }
            },
            '0'..='9' => self.lex_number(),
            'a'..='z' | 'A'..='Z' => self.lex_ident_or_keyword(),
            _ => Err(LexError {
                message: format!("Unexpected character '{}'", self.current_char()),
                line: self.pos.line,
                column: self.pos.column,
            }),
        };
        self.advance();
        res
    }

    pub fn lex_number(&mut self) -> LexResult<Token> {
        let start_pos = self.pos;
        while self.peek().is_numeric() {
            self.advance();
        }
        let text = &self.input[start_pos.index..self.pos.index + 1];
        let value = text.parse::<i32>().map_err(|_| LexError {
            message: format!("Invalid number: '{text}'"),
            line: start_pos.line,
            column: start_pos.column,
        })?;
        Ok(Token {
            ty: TokenType::Integer(value),
            span: Span {
                start_pos,
                end_pos: self.pos,
            },
        })
    }

    pub fn lex_ident_or_keyword(&mut self) -> LexResult<Token> {
        let start_pos = self.pos;
        while self.peek().is_alphanumeric() || self.peek() == '_' {
            self.advance();
        }
        let text = &self.input[start_pos.index..self.pos.index + 1];
        let ty = match text {
            "if" => TokenType::If,
            "else" => TokenType::Else,
            "while" => TokenType::While,
            "loop" => TokenType::Loop,
            "let" => TokenType::Let,
            "bool" => TokenType::Bool,
            "true" => TokenType::True,
            "false" => TokenType::False,
            "fn" => TokenType::Fn,
            "i32" => TokenType::I32,
            _ => TokenType::Identifier(text.to_string()),
        };
        Ok(Token {
            ty,
            span: Span {
                start_pos,
                end_pos: self.pos,
            },
        })
    }

    pub fn is_end(&self) -> bool {
        self.pos.index >= self.input.len()
    }

    pub fn advance(&mut self) {
        self.pos.index += 1;
        self.pos.column += 1;
        if self.current_char() == '\n' {
            self.pos.index += 1;
            self.pos.line += 1;
            self.pos.column = 1;
        }
    }

    pub fn current_char(&self) -> char {
        self.input.chars().nth(self.pos.index).unwrap_or('\0')
    }

    pub fn peek(&self) -> char {
        self.input.chars().nth(self.pos.index + 1).unwrap_or('\0')
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_operators() {
        let mut lexer = Lexer::new("+ - * / %");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 5);
        assert_eq!(tokens[0].ty, TokenType::Plus);
        assert_eq!(tokens[1].ty, TokenType::Minus);
        assert_eq!(tokens[2].ty, TokenType::Star);
        assert_eq!(tokens[3].ty, TokenType::Slash);
        assert_eq!(tokens[4].ty, TokenType::Percent);
    }

    #[test]
    fn test_comparison_operators() {
        let mut lexer = Lexer::new("== != < <= > >=");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 6);
        assert_eq!(tokens[0].ty, TokenType::Equal);
        assert_eq!(tokens[1].ty, TokenType::NotEqual);
        assert_eq!(tokens[2].ty, TokenType::Less);
        assert_eq!(tokens[3].ty, TokenType::LessEqual);
        assert_eq!(tokens[4].ty, TokenType::Greater);
        assert_eq!(tokens[5].ty, TokenType::GreaterEqual);
    }

    #[test]
    fn test_assignment_and_arrow() {
        let mut lexer = Lexer::new("= -> :");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].ty, TokenType::Assign);
        assert_eq!(tokens[1].ty, TokenType::Arrow);
        assert_eq!(tokens[2].ty, TokenType::Colon);
    }

    #[test]
    fn test_delimiters() {
        let mut lexer = Lexer::new("( ) [ ] { } ; ,");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 8);
        assert_eq!(tokens[0].ty, TokenType::LeftParen);
        assert_eq!(tokens[1].ty, TokenType::RightParen);
        assert_eq!(tokens[2].ty, TokenType::LeftBracket);
        assert_eq!(tokens[3].ty, TokenType::RightBracket);
        assert_eq!(tokens[4].ty, TokenType::LeftBrace);
        assert_eq!(tokens[5].ty, TokenType::RightBrace);
        assert_eq!(tokens[6].ty, TokenType::Semicolon);
        assert_eq!(tokens[7].ty, TokenType::Comma);
    }

    #[test]
    fn test_keywords() {
        let mut lexer = Lexer::new("let if else while loop bool true false fn i32");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 10);
        assert_eq!(tokens[0].ty, TokenType::Let);
        assert_eq!(tokens[1].ty, TokenType::If);
        assert_eq!(tokens[2].ty, TokenType::Else);
        assert_eq!(tokens[3].ty, TokenType::While);
        assert_eq!(tokens[4].ty, TokenType::Loop);
        assert_eq!(tokens[5].ty, TokenType::Bool);
        assert_eq!(tokens[6].ty, TokenType::True);
        assert_eq!(tokens[7].ty, TokenType::False);
        assert_eq!(tokens[8].ty, TokenType::Fn);
        assert_eq!(tokens[9].ty, TokenType::I32);
    }

    #[test]
    fn test_integers() {
        let mut lexer = Lexer::new("123 0 456");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].ty, TokenType::Integer(123));
        assert_eq!(tokens[1].ty, TokenType::Integer(0));
        assert_eq!(tokens[2].ty, TokenType::Integer(456));
    }

    #[test]
    fn test_negative_numbers() {
        let mut lexer = Lexer::new("-123 -0");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].ty, TokenType::Integer(-123));
        assert_eq!(tokens[1].ty, TokenType::Integer(0));
    }

    #[test]
    fn test_identifiers() {
        let mut lexer = Lexer::new("hello world_var camelCase UPPER_CASE");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 4);
        assert_eq!(tokens[0].ty, TokenType::Identifier("hello".to_string()));
        assert_eq!(tokens[1].ty, TokenType::Identifier("world_var".to_string()));
        assert_eq!(tokens[2].ty, TokenType::Identifier("camelCase".to_string()));
        assert_eq!(tokens[3].ty, TokenType::Identifier("UPPER_CASE".to_string()));
    }

    #[test]
    fn test_single_line_comments() {
        let mut lexer = Lexer::new("123 // this is a comment\n456");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].ty, TokenType::Integer(123));
        assert_eq!(tokens[1].ty, TokenType::Integer(456));
    }

    #[test]
    fn test_multi_line_comments() {
        let mut lexer = Lexer::new("123 /* this is a\nmulti-line comment */ 456");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].ty, TokenType::Integer(123));
        assert_eq!(tokens[1].ty, TokenType::Integer(456));
    }

    #[test]
    fn test_nested_multi_line_comments() {
        let mut lexer = Lexer::new("123 /* outer /* inner */ outer */ 456");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].ty, TokenType::Integer(123));
        assert_eq!(tokens[1].ty, TokenType::Integer(456));
    }

    #[test]
    fn test_unterminated_comment_error() {
        let mut lexer = Lexer::new("123 /* unterminated comment");
        let result = lexer.tokenize();
        
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert!(error.message.contains("Unterminated multi-line comment"));
    }

    #[test]
    fn test_function_declaration() {
        let mut lexer = Lexer::new("fn add(x: i32, y: i32) -> i32 { x + y }");
        let tokens = lexer.tokenize().unwrap();
        
        let expected_types = vec![
            TokenType::Fn,
            TokenType::Identifier("add".to_string()),
            TokenType::LeftParen,
            TokenType::Identifier("x".to_string()),
            TokenType::Colon,
            TokenType::I32,
            TokenType::Comma,
            TokenType::Identifier("y".to_string()),
            TokenType::Colon,
            TokenType::I32,
            TokenType::RightParen,
            TokenType::Arrow,
            TokenType::I32,
            TokenType::LeftBrace,
            TokenType::Identifier("x".to_string()),
            TokenType::Plus,
            TokenType::Identifier("y".to_string()),
            TokenType::RightBrace,
        ];
        
        assert_eq!(tokens.len(), expected_types.len());
        for (i, expected) in expected_types.iter().enumerate() {
            assert_eq!(tokens[i].ty, *expected);
        }
    }

    #[test]
    fn test_not_operator() {
        let mut lexer = Lexer::new("! != x");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].ty, TokenType::Not);
        assert_eq!(tokens[1].ty, TokenType::NotEqual);
        assert_eq!(tokens[2].ty, TokenType::Identifier("x".to_string()));
    }

    #[test]
    fn test_empty_input() {
        let mut lexer = Lexer::new("");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 0);
    }

    #[test]
    fn test_whitespace_only() {
        let mut lexer = Lexer::new("   \n\t  ");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 0);
    }

    #[test]
    fn test_complex_expression() {
        let mut lexer = Lexer::new("let x = (a + b) * c - d / e % f;");
        let tokens = lexer.tokenize().unwrap();
        
        let expected_types = vec![
            TokenType::Let,
            TokenType::Identifier("x".to_string()),
            TokenType::Assign,
            TokenType::LeftParen,
            TokenType::Identifier("a".to_string()),
            TokenType::Plus,
            TokenType::Identifier("b".to_string()),
            TokenType::RightParen,
            TokenType::Star,
            TokenType::Identifier("c".to_string()),
            TokenType::Minus,
            TokenType::Identifier("d".to_string()),
            TokenType::Slash,
            TokenType::Identifier("e".to_string()),
            TokenType::Percent,
            TokenType::Identifier("f".to_string()),
            TokenType::Semicolon,
        ];
        
        assert_eq!(tokens.len(), expected_types.len());
        for (i, expected) in expected_types.iter().enumerate() {
            assert_eq!(tokens[i].ty, *expected);
        }
    }

    #[test]
    fn test_conditional_expression() {
        let mut lexer = Lexer::new("if x == y && z > 10 { true } else { false }");
        let tokens = lexer.tokenize().unwrap();
        
        let expected_types = vec![
            TokenType::If,
            TokenType::Identifier("x".to_string()),
            TokenType::Equal,
            TokenType::Identifier("y".to_string()),
            TokenType::LogicAnd,
            TokenType::Identifier("z".to_string()),
            TokenType::Greater,
            TokenType::Integer(10),
            TokenType::LeftBrace,
            TokenType::True,
            TokenType::RightBrace,
            TokenType::Else,
            TokenType::LeftBrace,
            TokenType::False,
            TokenType::RightBrace,
        ];
        
        assert_eq!(tokens.len(), expected_types.len());
        for (i, expected) in expected_types.iter().enumerate() {
            assert_eq!(tokens[i].ty, *expected);
        }
    }

    #[test]
    fn test_position_tracking() {
        let mut lexer = Lexer::new("let x = 42;\nif true { }");
        let tokens = lexer.tokenize().unwrap();
        
        // 测试第一个token的位置
        assert_eq!(tokens[0].span.start_pos.line, 1);
        assert_eq!(tokens[0].span.start_pos.column, 1);
        
        // 找到第二行的if token
        let if_token = tokens.iter().find(|t| matches!(t.ty, TokenType::If)).unwrap();
        assert_eq!(if_token.span.start_pos.line, 2);
    }

    #[test]
    fn test_invalid_character_error() {
        let mut lexer = Lexer::new("let x = @;");
        let result = lexer.tokenize();
        
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert!(error.message.contains("Unexpected character"));
    }

    #[test]
    fn test_large_number_overflow() {
        let mut lexer = Lexer::new("999999999999999999999");
        let result = lexer.tokenize();
        
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert!(error.message.contains("Invalid number"));
    }

    #[test]
    fn test_minus_vs_negative_number() {
        let mut lexer = Lexer::new("x - 5 -10");
        let tokens = lexer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 4);
        assert_eq!(tokens[0].ty, TokenType::Identifier("x".to_string()));
        assert_eq!(tokens[1].ty, TokenType::Minus);
        assert_eq!(tokens[2].ty, TokenType::Integer(5));
        assert_eq!(tokens[3].ty, TokenType::Integer(-10));
    }
    
}

