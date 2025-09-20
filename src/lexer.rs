// Copyright (c) 2025 Lina Butler
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::str::CharIndices;

use itertools::PeekNth;

use super::error::{LexicalError, SpannedError};

/// A token produced by the [`Lexer`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Token<'input> {
    Alternative,  // //
    Equal,        // ==
    NotEqual,     // !=
    LessEqual,    // <=
    GreaterEqual, // >=
    DotDot,       // ..

    Pipe,         // |
    Less,         // <
    Greater,      // >
    Plus,         // +
    Minus,        // -
    Multiply,     // *
    Divide,       // /
    Modulo,       // %
    Question,     // ?
    Dot,          // .
    LeftBracket,  // [
    RightBracket, // ]
    LeftBrace,    // {
    RightBrace,   // }
    LeftParen,    // (
    RightParen,   // )
    Colon,        // :
    Semicolon,    // ;
    Comma,        // ,

    And,   // and
    Or,    // or
    Not,   // not
    True,  // true
    False, // false
    Null,  // null

    Number(&'input str), // Integer or floating-point number.
    String(&'input str), // Single or double-quoted string.
    Ident(&'input str),  // Unquoted identifier.
}

/// A lexer for the `jqish` grammar.
///
/// We use a custom lexer instead of LARLPOP's default because
/// the grammar is easier to lex character-by-character: in particular,
/// strings and numbers are much harder to lex with regular expressions.
pub struct Lexer<'input> {
    cursor: PeekNth<CharIndices<'input>>,
    input: &'input str,
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Result<(usize, Token<'input>, usize), SpannedError<LexicalError>>;

    fn next(&mut self) -> Option<Self::Item> {
        // Record the starting position before advancing the cursor,
        // so that we can report accurate location info.
        let &(start, _) = self.cursor.peek()?;

        let token = {
            self.skip_whitespace();

            // Try to consume the next token.
            self.try_string()
                .or_else(|| Some(Ok(self.try_number()?)))
                .or_else(|| Some(Ok(self.try_keyword_or_ident()?)))
                .or_else(|| Some(Ok(self.try_operator()?)))
                .or_else(|| {
                    // Either we've reached the end of the input,
                    // or we have an unexpected token.
                    let &(_, c) = self.cursor.peek()?;
                    Some(Err(LexicalError::Unexpected(c)))
                })
        }?;

        let end = self
            .cursor
            .peek()
            .map(|&(at, _)| at + 1)
            .unwrap_or_else(|| self.input.len());

        Some(
            token
                .map(|token| (start, token, end))
                .map_err(|err| SpannedError {
                    error: err,
                    location: (start, end),
                }),
        )
    }
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer {
            cursor: itertools::peek_nth(input.char_indices()),
            input,
        }
    }

    /// Advances the cursor past any whitespace tokens at the
    /// current position.
    fn skip_whitespace(&mut self) {
        while let Some(&(_, c)) = self.cursor.peek()
            && c.is_whitespace()
        {
            self.cursor.next();
        }
    }

    /// Consumes a single or double-quoted string at the current position.
    /// The resulting [`Token::String`] includes the quotes.
    fn try_string(&mut self) -> Option<Result<Token<'input>, LexicalError>> {
        let (start, quote) = self.cursor.next_if(|&(_, c)| c == '"' || c == '\'')?;
        while let Some((at, c)) = self.cursor.next() {
            match c {
                '\\' => {
                    // Skip over escaped characters; we'll validate
                    // escape sequences at parse time.
                    self.cursor.next();
                }
                // A matching (unescaped) quote marks the end of the string.
                c if c == quote => return Some(Ok(Token::String(&self.input[start..=at]))),
                _ => continue,
            }
        }
        Some(Err(LexicalError::UnterminatedString))
    }

    /// Consumes an integer or floating-point number at the current position.
    ///
    /// Numbers are always positive; negative numbers are lexed as
    /// two separate tokens (`Minus` and `Number`).
    fn try_number(&mut self) -> Option<Token<'input>> {
        #[derive(Clone, Copy)]
        enum State {
            Integer,
            Decimal,
            Exponent,
        }

        let (start, mut state, mut end) = match *(self.cursor.peek_nth(0)?) {
            // An integer: `5`.
            (at, c) if c.is_ascii_digit() => {
                self.cursor.nth(0);
                (at, State::Integer, at)
            }
            // A decimal without an integer component: `.5`.
            (start, '.') => match self.cursor.peek_nth(1)? {
                &(end, c) if c.is_ascii_digit() => {
                    self.cursor.nth(1);
                    (start, State::Decimal, end)
                }
                _ => return None,
            },
            _ => return None,
        };

        while let Some(&(at, c)) = self.cursor.peek() {
            (state, end) = match (state, c) {
                (state, c) if c.is_ascii_digit() => {
                    self.cursor.next();
                    (state, at)
                }
                (State::Integer, '.') => {
                    self.cursor.next();
                    (State::Decimal, at)
                }
                (State::Integer | State::Decimal, 'e' | 'E') => {
                    self.cursor.next();
                    let at = match self.cursor.peek() {
                        Some(&(at, '+')) | Some(&(at, '-')) => {
                            self.cursor.next();
                            at
                        }
                        _ => at,
                    };
                    (State::Exponent, at)
                }
                _ => break,
            };
        }

        Some(Token::Number(&self.input[start..=end]))
    }

    /// Consumes an operator at the current position.
    fn try_operator(&mut self) -> Option<Token<'input>> {
        let (start, token, end) = match (
            self.cursor.peek_nth(0).copied()?,
            self.cursor.peek_nth(1).copied(),
        ) {
            ((start, '/'), Some((end, '/'))) => (start, Token::Alternative, end),
            ((start, '='), Some((end, '='))) => (start, Token::Equal, end),
            ((start, '!'), Some((end, '='))) => (start, Token::NotEqual, end),
            ((start, '<'), Some((end, '='))) => (start, Token::LessEqual, end),
            ((start, '>'), Some((end, '='))) => (start, Token::GreaterEqual, end),
            ((start, '.'), Some((end, '.'))) => (start, Token::DotDot, end),

            ((at, '|'), _) => (at, Token::Pipe, at),
            ((at, '<'), _) => (at, Token::Less, at),
            ((at, '>'), _) => (at, Token::Greater, at),
            ((at, '+'), _) => (at, Token::Plus, at),
            ((at, '-'), _) => (at, Token::Minus, at),
            ((at, '*'), _) => (at, Token::Multiply, at),
            ((at, '/'), _) => (at, Token::Divide, at),
            ((at, '%'), _) => (at, Token::Modulo, at),
            ((at, '?'), _) => (at, Token::Question, at),
            ((at, '.'), _) => (at, Token::Dot, at),
            ((at, '['), _) => (at, Token::LeftBracket, at),
            ((at, ']'), _) => (at, Token::RightBracket, at),
            ((at, '{'), _) => (at, Token::LeftBrace, at),
            ((at, '}'), _) => (at, Token::RightBrace, at),
            ((at, '('), _) => (at, Token::LeftParen, at),
            ((at, ')'), _) => (at, Token::RightParen, at),
            ((at, ':'), _) => (at, Token::Colon, at),
            ((at, ';'), _) => (at, Token::Semicolon, at),
            ((at, ','), _) => (at, Token::Comma, at),

            _ => return None,
        };
        self.cursor.nth(end - start);
        Some(token)
    }

    /// Consumes a keyword (operator or literal) or an unquoted identifier
    /// at the current position.
    fn try_keyword_or_ident(&mut self) -> Option<Token<'input>> {
        let (start, _) = self
            .cursor
            .next_if(|&(_, c)| c.is_ascii_alphabetic() || c == '_')?;
        let mut end = start;

        while let Some(&(at, c)) = self.cursor.peek()
            && (c.is_ascii_alphanumeric() || c == '_')
        {
            self.cursor.next();
            end = at;
        }

        Some(match &self.input[start..=end] {
            "and" => Token::And,
            "or" => Token::Or,
            "not" => Token::Not,
            "true" => Token::True,
            "false" => Token::False,
            "null" => Token::Null,
            other => Token::Ident(other),
        })
    }
}
