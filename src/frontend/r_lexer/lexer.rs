use crate::frontend::r_lexer::error::{LexError, LexResult};
use crate::frontend::r_lexer::token::{Position, Token, TokenType};
use regex::Regex;
use std::collections::HashMap;

#[derive(Debug, Clone)]
struct TokenRule {
    token_type: TokenType,
    pattern: Regex,
}

impl TokenRule {
    pub fn new(token_type: TokenType, pattern: &str) -> LexResult<Self> {
        let regex = Regex::new(pattern).map_err(|_| LexError::Generic {
            message: format!("Invalid regex pattern"),
            line: 0,
            column: 0,
        })?;

        Ok(Self {
            token_type,
            pattern: regex,
        })
    }
}

pub struct Lexer {
    rules: Vec<TokenRule>,
    keywords: HashMap<&'static str, TokenType>,
    input: String,
    pos: Position,
}

impl Lexer {
    pub fn new(input: String) -> LexResult<Self> {
        let mut lexer = Self {
            rules: Vec::new(),
            keywords: HashMap::new(),
            input,
            pos: Position::start(),
        };
        lexer.initialize()?;
        Ok(lexer)
    }

    pub fn initialize(&mut self) -> LexResult<()> {
        // Rules

        // Length = 3
        self.add_rule(TokenType::DotDotDot, r"\.\.\.")?;
        self.add_rule(TokenType::DotDotEq, r"\.\.\=")?;
        self.add_rule(TokenType::SLEq, r"<<=")?;
        self.add_rule(TokenType::SREq, r">>=")?;

        // Length = 2
        self.add_rule(TokenType::LEq, r"<=")?;
        self.add_rule(TokenType::GEq, r">=")?;
        self.add_rule(TokenType::NEq, r"!=")?;
        self.add_rule(TokenType::AndAnd, r"&&")?;
        self.add_rule(TokenType::OrOr, r"\|\|")?;
        self.add_rule(TokenType::RArrow, r"->")?;
        self.add_rule(TokenType::FatArrow, r"=>")?;
        self.add_rule(TokenType::EqEq, r"==")?;
        self.add_rule(TokenType::ModEq, r"%=")?;
        self.add_rule(TokenType::PlusEq, r"\+=")?;
        self.add_rule(TokenType::MinusEq, r"-=")?;
        self.add_rule(TokenType::MulEq, r"\*=")?;
        self.add_rule(TokenType::DivEq, r"/=")?;
        self.add_rule(TokenType::XorEq, r"\^=")?;
        self.add_rule(TokenType::AndEq, r"&=")?;
        self.add_rule(TokenType::OrEq, r"\|=")?;
        self.add_rule(TokenType::DotDot, r"\.\.")?;
        self.add_rule(TokenType::ColonColon, r"::")?;
        self.add_rule(TokenType::SL, r"<<")?;
        self.add_rule(TokenType::SR, r">>")?;
        self.add_rule(TokenType::LArrow, r"<-")?;

        // Number Literals
        self.add_rule(
            TokenType::FloatLiteral,
            r"^[+-]?(\d(?:_?\d)*\.(?:\d(?:_?\d)*)?|\.\d(?:_?\d)*)(f32|f64)?$",
        )?;
        self.add_rule(TokenType::IntegerLiteral,  r"[+-]?((0b[_01]*[01][_01]*)|(0o[_0-7]*[0-7][_0-7]*)|(0x[_0-9a-fA-F]*[0-9a-fA-F][_0-9a-fA-F]*)|([0-9][_0-9]*))(u32|i32|usize|isize)?")?;
        self.add_rule(TokenType::ReservedIntegerLiteral, r"[+-]?((0b[_0-9]*[0-9][_0-9]*)|(0o[_0-9]*[0-9][_0-9]*)|(0x[_0-9a-fA-F]*[0-9a-fA-F][_0-9a-fA-F]*)|([0-9][_0-9]*))(u32|i32|usize|isize)?")?;

        // Length = 1
        self.add_rule(TokenType::LBrace, r"\{")?;
        self.add_rule(TokenType::RBrace, r"\}")?;
        self.add_rule(TokenType::LBracket, r"\[")?;
        self.add_rule(TokenType::RBracket, r"\]")?;
        self.add_rule(TokenType::LParen, r"\(")?;
        self.add_rule(TokenType::RParen, r"\)")?;
        self.add_rule(TokenType::Eq, r"=")?;
        self.add_rule(TokenType::Lt, r"<")?;
        self.add_rule(TokenType::Gt, r">")?;
        self.add_rule(TokenType::Not, r"!")?;
        self.add_rule(TokenType::Tilde, r"~")?;
        self.add_rule(TokenType::Plus, r"\+")?;
        self.add_rule(TokenType::Minus, r"-")?;
        self.add_rule(TokenType::Mul, r"\*")?;
        self.add_rule(TokenType::Div, r"/")?;
        self.add_rule(TokenType::Percent, r"%")?;
        self.add_rule(TokenType::Xor, r"\^")?;
        self.add_rule(TokenType::And, r"&")?;
        self.add_rule(TokenType::Or, r"\|")?;
        self.add_rule(TokenType::At, r"@")?;
        self.add_rule(TokenType::Dot, r"\.")?;
        self.add_rule(TokenType::Comma, r",")?;
        self.add_rule(TokenType::Semicolon, r";")?;
        self.add_rule(TokenType::Colon, r":")?;
        self.add_rule(TokenType::Pound, r"#")?;
        self.add_rule(TokenType::Dollar, r"\$")?;
        self.add_rule(TokenType::Question, r"\?")?;
        self.add_rule(TokenType::Underscore, r"_")?;

        // String Literals
        self.add_rule(TokenType::StringLiteral, r#""(?:\\.|[^\\"])*""#)?;
        self.add_rule(TokenType::RawStringLiteral, r#"r(#?)"(?s)(.*?)"(#?)"#)?;
        self.add_rule(TokenType::ByteStringLiteral, r#"b"(?:\\.|[^\\"])*""#)?;
        self.add_rule(TokenType::RawByteStringLiteral, r#"br(#?)\"(.*?)\"(#?)"#)?;
        self.add_rule(TokenType::CStringLiteral, r#"c"(?:\\.|[^\\"])*""#)?;
        self.add_rule(TokenType::RawCStringLiteral, r#"cr(#?)\"(.*?)\"(#?)"#)?;
        self.add_rule(
            TokenType::CharLiteral,
            r#"('([^'\\\n\r\t]|\\[nrt'"\\0]|\\x[0-7][0-9a-fA-F])')"#,
        )?;
        self.add_rule(
            TokenType::ByteLiteral,
            r#"(b'([^'\\\n\r\t]|\\[nrt'"\\0]|\\x[0-7][0-9a-fA-F])')"#,
        )?;

        // Identifiers
        self.add_rule(TokenType::Identifier, r"[a-zA-Z][a-zA-Z0-9_]*")?;

        // Keywords
        let keywords = [
            ("as", TokenType::As),
            ("break", TokenType::Break),
            ("const", TokenType::Const),
            ("continue", TokenType::Continue),
            ("crate", TokenType::Crate),
            ("else", TokenType::Else),
            ("enum", TokenType::Enum),
            ("extern", TokenType::Extern),
            ("false", TokenType::False),
            ("fn", TokenType::Fn),
            ("for", TokenType::For),
            ("if", TokenType::If),
            ("impl", TokenType::Impl),
            ("in", TokenType::In),
            ("let", TokenType::Let),
            ("loop", TokenType::Loop),
            ("match", TokenType::Match),
            ("mod", TokenType::Mod),
            ("move", TokenType::Move),
            ("mut", TokenType::Mut),
            ("pub", TokenType::Pub),
            ("ref", TokenType::Ref),
            ("return", TokenType::Return),
            ("self", TokenType::SelfLower),
            ("Self", TokenType::SelfUpper),
            ("static", TokenType::Static),
            ("struct", TokenType::Struct),
            ("super", TokenType::Super),
            ("trait", TokenType::Trait),
            ("true", TokenType::True),
            ("type", TokenType::Type),
            ("unsafe", TokenType::Unsafe),
            ("use", TokenType::Use),
            ("where", TokenType::Where),
            ("while", TokenType::While),
            ("async", TokenType::Async),
            ("await", TokenType::Await),
            ("dyn", TokenType::Dyn),
            ("abstract", TokenType::Abstract),
            ("become", TokenType::Become),
            ("box", TokenType::Box),
            ("do", TokenType::Do),
            ("final", TokenType::Final),
            ("macro", TokenType::Macro),
            ("override", TokenType::Override),
            ("priv", TokenType::Priv),
            ("typeof", TokenType::Typeof),
            ("unsized", TokenType::Unsized),
            ("virtual", TokenType::Virtual),
            ("yield", TokenType::Yield),
            ("try", TokenType::Try),
        ];

        for (keyword, token_type) in keywords {
            self.keywords.insert(keyword, token_type);
        }

        Ok(())
    }

    fn add_rule(&mut self, token_type: TokenType, pattern: &str) -> LexResult<()> {
        let anchored_pattern = if !pattern.starts_with('^') {
            format!("^{}", pattern)
        } else {
            pattern.to_string()
        };
        let rule = TokenRule::new(token_type, &anchored_pattern)?;
        self.rules.push(rule);
        Ok(())
    }

    pub fn tokenize(&mut self) -> LexResult<Vec<Token>> {
        let mut tokens = Vec::new();

        while !self.is_end() {
            self.skip_whitespace_and_comments()?;
            if !self.is_end() {
                tokens.push(self.next_token()?);
            }
        }
        tokens.push(Token {
            token_type: TokenType::Eof,
            lexeme: String::new(),
            position: self.pos.clone(),
        });

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
            return Err(LexError::Generic {
                message: "Unterminated multi-line comment".to_string(),
                line: start_line,
                column: start_column,
            });
        }

        Ok(())
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
        self.input[self.pos.index..].chars().next().unwrap_or('\0')
    }

    pub fn peek(&self) -> char {
        self.input[self.pos.index + 1..]
            .chars()
            .next()
            .unwrap_or('\0')
    }

    pub fn is_end(&self) -> bool {
        self.pos.index >= self.input.len()
    }

    pub fn next_token(&mut self) -> LexResult<Token> {
        let remaining = &self.input[self.pos.index..];
        let mut match_token: Option<Token> = None;
        for rule in &self.rules {
            if let Some(mat) = rule.pattern.find(remaining) {
                let lexeme = mat.as_str().to_string();
                let position = self.pos.clone();
                self.pos.index += lexeme.len();
                self.pos.column += lexeme.len();
                if self.current_char() == '\n' {
                    self.pos.index += 1;
                    self.pos.line += 1;
                    self.pos.column = 1;
                }
                match_token = Some(Token {
                    token_type: rule.token_type,
                    lexeme,
                    position,
                });

                break;
            }
        }

        if let Some(token) = match_token {
            if token.token_type == TokenType::Identifier {
                if let Some(&keyword_type) = self.keywords.get(token.lexeme.as_str()) {
                    return Ok(Token {
                        token_type: keyword_type,
                        lexeme: token.lexeme,
                        position: token.position,
                    });
                }
            }
            return Ok(token);
        }

        Err(LexError::InvalidToken {
            text: self.current_char().to_string(),
            line: self.pos.line,
            column: self.pos.column,
        })
    }
}
