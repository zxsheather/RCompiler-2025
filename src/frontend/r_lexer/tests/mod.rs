use crate::frontend::r_lexer::lexer::Lexer;
use crate::frontend::r_lexer::token::TokenType;

#[test]
fn test_keywords() {
    let mut lexer = Lexer::new("fn let mut if else while".to_string()).unwrap();
    let tokens = lexer.tokenize().unwrap();

    assert_eq!(tokens.len(), 7);
    assert_eq!(tokens[0].token_type, TokenType::Fn);
    assert_eq!(tokens[1].token_type, TokenType::Let);
    assert_eq!(tokens[2].token_type, TokenType::Mut);
    assert_eq!(tokens[3].token_type, TokenType::If);
    assert_eq!(tokens[4].token_type, TokenType::Else);
    assert_eq!(tokens[5].token_type, TokenType::While);
    assert_eq!(tokens[6].token_type, TokenType::Eof);
}

#[test]
fn test_identifiers() {
    let mut lexer = Lexer::new("variable_name CamelCase".to_string()).unwrap();
    let tokens = lexer.tokenize().unwrap();
    // println!("{:?}", tokens);

    assert_eq!(tokens.len(), 3); // 2 identifiers + EOF
    assert_eq!(tokens[0].token_type, TokenType::Identifier);
    assert_eq!(tokens[0].lexeme, "variable_name");
    assert_eq!(tokens[1].token_type, TokenType::Identifier);
    assert_eq!(tokens[1].lexeme, "CamelCase");
}

#[test]
fn test_string_literals() {
    let mut lexer = Lexer::new(r#""hello" "world\n" b"bytes" r"raw""#.to_string()).unwrap();
    let tokens = lexer.tokenize().unwrap();
    // println!("{:?}", tokens);
    assert_eq!(tokens.len(), 5); // 4 strings + EOF
    assert_eq!(tokens[0].token_type, TokenType::StringLiteral);
    assert_eq!(tokens[0].lexeme, r#""hello""#);
    assert_eq!(tokens[1].token_type, TokenType::StringLiteral);
    assert_eq!(tokens[1].lexeme, r#""world\n""#);
    assert_eq!(tokens[2].token_type, TokenType::ByteStringLiteral);
    assert_eq!(tokens[2].lexeme, r#"b"bytes""#);
    assert_eq!(tokens[3].token_type, TokenType::RawStringLiteral);
    assert_eq!(tokens[3].lexeme, r#"r"raw""#);
}

#[test]
fn test_character_literals() {
    let mut lexer = Lexer::new("'a' '\\n' '\\x41' b'B'".to_string()).unwrap();
    let tokens = lexer.tokenize().unwrap();

    assert_eq!(tokens.len(), 5); // 4 chars + EOF
    assert_eq!(tokens[0].token_type, TokenType::CharLiteral);
    assert_eq!(tokens[0].lexeme, "'a'");
    assert_eq!(tokens[1].token_type, TokenType::CharLiteral);
    assert_eq!(tokens[1].lexeme, "'\\n'");
    assert_eq!(tokens[2].token_type, TokenType::CharLiteral);
    assert_eq!(tokens[2].lexeme, "'\\x41'");
    assert_eq!(tokens[3].token_type, TokenType::ByteLiteral);
    assert_eq!(tokens[3].lexeme, "b'B'");
}

#[test]
fn test_operators() {
    let mut lexer = Lexer::new("+ - * / % == != <= >= && || -> =>".to_string()).unwrap();
    let tokens = lexer.tokenize().unwrap();

    let expected_types = [
        TokenType::Plus,
        TokenType::Minus,
        TokenType::Mul,
        TokenType::Div,
        TokenType::Percent,
        TokenType::EqEq,
        TokenType::NEq,
        TokenType::LEq,
        TokenType::GEq,
        TokenType::AndAnd,
        TokenType::OrOr,
        TokenType::RArrow,
        TokenType::FatArrow,
        TokenType::Eof,
    ];

    assert_eq!(tokens.len(), expected_types.len());
    for (token, expected) in tokens.iter().zip(expected_types.iter()) {
        assert_eq!(token.token_type, *expected);
    }
}

#[test]
fn test_punctuation() {
    let mut lexer = Lexer::new("{ } [ ] ( ) , ; : :: .".to_string()).unwrap();
    let tokens = lexer.tokenize().unwrap();

    let expected_types = [
        TokenType::LBrace,
        TokenType::RBrace,
        TokenType::LBracket,
        TokenType::RBracket,
        TokenType::LParen,
        TokenType::RParen,
        TokenType::Comma,
        TokenType::Semicolon,
        TokenType::Colon,
        TokenType::ColonColon,
        TokenType::Dot,
        TokenType::Eof,
    ];

    assert_eq!(tokens.len(), expected_types.len());
    for (token, expected) in tokens.iter().zip(expected_types.iter()) {
        assert_eq!(token.token_type, *expected);
    }
}

#[test]
fn test_position_tracking() {
    let mut lexer = Lexer::new("fn\nmain() {\n    let x = 42;\n}".to_string()).unwrap();
    let tokens = lexer.tokenize().unwrap();
    // println!("{:?}", tokens);
    assert_eq!(tokens[0].position.line, 1);
    assert_eq!(tokens[0].position.column, 1);
    assert_eq!(tokens[1].position.line, 2); // main on line 2
    assert_eq!(tokens[1].position.column, 1);
    // Find the "let" token
    let let_token = tokens.iter().find(|t| t.lexeme == "let").unwrap();
    assert_eq!(let_token.position.line, 3);
    assert_eq!(let_token.position.column, 5); // after 4 spaces
}

#[test]
fn test_invalid_token_error() {
    let mut lexer = Lexer::new("let x = @@@".to_string()).unwrap();
    let result = lexer.tokenize(); // Use filtered to avoid whitespace

    match result {
        Ok(tokens) => {
            // Should have let, x, =, @, @, @, EOF
            assert!(tokens.len() >= 4);
            assert_eq!(tokens[0].token_type, TokenType::Let);
            assert_eq!(tokens[1].token_type, TokenType::Identifier);
            assert_eq!(tokens[2].token_type, TokenType::Eq);
            assert_eq!(tokens[3].token_type, TokenType::At);
        }
        Err(_) => {
            // This is also acceptable if it errors on invalid sequence
        }
    }
}

#[test]
fn test_complex_expression() {
    let source =
        "fn fibonacci(n: u32) -> u32 { if n <= 1 { n } else { fibonacci(n-1) + fibonacci(n-2) } }";
    let mut lexer = Lexer::new(source.to_string()).unwrap();
    let tokens = lexer.tokenize().unwrap();

    // Should start with fn, fibonacci, (, n, :, u32, ), -, >, u32, {
    assert_eq!(tokens[0].token_type, TokenType::Fn);
    assert_eq!(tokens[1].token_type, TokenType::Identifier);
    assert_eq!(tokens[1].lexeme, "fibonacci");
    assert_eq!(tokens[2].token_type, TokenType::LParen);
    assert_eq!(tokens[3].token_type, TokenType::Identifier);
    assert_eq!(tokens[3].lexeme, "n");
    assert_eq!(tokens[4].token_type, TokenType::Colon);
    assert_eq!(tokens[5].token_type, TokenType::U32);
    assert_eq!(tokens[5].lexeme, "u32");
    assert_eq!(tokens[6].token_type, TokenType::RParen);
    assert_eq!(tokens[7].token_type, TokenType::RArrow);
}

#[test]
fn test_self_vs_self_upper() {
    let mut lexer = Lexer::new("self Self".to_string()).unwrap();
    let tokens = lexer.tokenize().unwrap();

    assert_eq!(tokens.len(), 3); // self, Self, EOF
    assert_eq!(tokens[0].token_type, TokenType::SelfLower);
    assert_eq!(tokens[0].lexeme, "self");
    assert_eq!(tokens[1].token_type, TokenType::SelfUpper);
    assert_eq!(tokens[1].lexeme, "Self");
}

#[test]
fn test_operator_precedence_parsing() {
    // Test that longer operators are matched before shorter ones
    let mut lexer = Lexer::new("<<= << <= <".to_string()).unwrap();
    let tokens = lexer.tokenize().unwrap();

    assert_eq!(tokens.len(), 5); // 4 operators + EOF
    assert_eq!(tokens[0].token_type, TokenType::SLEq);
    assert_eq!(tokens[0].lexeme, "<<=");
    assert_eq!(tokens[1].token_type, TokenType::SL);
    assert_eq!(tokens[1].lexeme, "<<");
    assert_eq!(tokens[2].token_type, TokenType::LEq);
    assert_eq!(tokens[2].lexeme, "<=");
    assert_eq!(tokens[3].token_type, TokenType::Lt);
    assert_eq!(tokens[3].lexeme, "<");
}

#[test]
fn test_unicode_string_literal() {
    let mut lexer = Lexer::new(r#""你好，世界" fn"#.to_string()).unwrap();
    let tokens = lexer.tokenize().unwrap();

    assert_eq!(tokens[0].token_type, TokenType::StringLiteral);
    assert_eq!(tokens[0].lexeme, r#""你好，世界""#);
    assert_eq!(tokens[1].token_type, TokenType::Fn);
    assert_eq!(tokens[1].position.line, 1);
    // Column should account for UTF-8 string width (quote + 5 chars + quote + space)
    assert_eq!(tokens[1].position.column, 9);
    assert_eq!(tokens.last().unwrap().token_type, TokenType::Eof);
}

#[test]
fn test_unicode_comment_and_identifier_position() {
    let mut lexer = Lexer::new("// 注释包含Unicode\nfn main() {}".to_string()).unwrap();
    let tokens = lexer.tokenize().unwrap();

    assert_eq!(tokens[0].token_type, TokenType::Fn);
    assert_eq!(tokens[0].position.line, 2);
    assert_eq!(tokens[0].position.column, 1);
    assert_eq!(tokens[1].token_type, TokenType::Identifier);
    assert_eq!(tokens[1].lexeme, "main");
    assert_eq!(tokens[1].position.line, 2);
    assert_eq!(tokens[1].position.column, 4);
}
