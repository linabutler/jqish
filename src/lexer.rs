// Copyright (c) 2025 Lina Butler
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::ops::Range;

use logos::Logos;

use super::error::{LexicalError, SpannedError};

/// A token produced by the [`Lexer`].
#[derive(Clone, Debug, Eq, Logos, PartialEq)]
pub enum Token<'input> {
    #[token("?//")]
    Alternation,
    #[token("//")]
    Alt,
    #[token("==")]
    Equal,
    #[token("!=")]
    NotEqual,
    #[token("<=")]
    LessEqual,
    #[token(">=")]
    GreaterEqual,

    #[token("|")]
    Pipe,
    #[token("<")]
    Less,
    #[token(">")]
    Greater,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Multiply,
    #[token("/")]
    Divide,
    #[token("%")]
    Modulo,
    #[token("?")]
    Question,
    #[token(".")]
    Dot,
    #[token("[")]
    LeftBracket,
    #[token("]")]
    RightBracket,
    #[token("{")]
    LeftBrace,
    #[token("}")]
    RightBrace,
    #[token("(")]
    LeftParen,
    #[token(")")]
    RightParen,
    #[token(":")]
    Colon,
    #[token(";")]
    Semicolon,
    #[token(",")]
    Comma,
    #[token("$")]
    Dollar,

    #[token("and")]
    And,
    #[token("or")]
    Or,
    #[token("not")]
    Not,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("null")]
    Null,
    #[token("as")]
    As,

    /// Integer or floating-point number.
    #[regex(r"\.[0-9]+(?:[eE][+-]?[0-9]+)?", |lex| lex.slice())]
    #[regex(r"(?:0|[1-9][0-9]*)(?:\.[0-9]*)?(?:[eE][+-]?[0-9]+)?", |lex| lex.slice())]
    Number(&'input str),

    /// Single- or double-quoted string.
    #[regex(r#"["']"#, lex_string)]
    String((usize, StringSegments<'input>, usize)),

    /// Unquoted identifier.
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice())]
    Ident(&'input str),

    /// Skipped whitespace or invalid token.
    #[regex(r"[[:space:]]*", logos::skip)]
    #[error]
    Error,
}

/// A context-dependent lexer for a string.
#[derive(Clone, Copy, Debug, Eq, Logos, PartialEq)]
pub enum StringToken<'input> {
    #[regex(r#"[^"'\\]+"#, |lex| lex.slice())]
    Content(&'input str),

    // Note: we don't support `\b`, `\f`, or `\uHHHH`
    // escape sequences.
    #[regex(r#"\\[nrt\\'"]"#, |lex| lex.slice().chars().nth(1))]
    Escape(char),

    #[token(r#"\("#)]
    InterpolationStart,

    #[regex(r#"['"]"#, |lex| lex.slice())]
    Quote(&'input str),

    #[error]
    Error,
}

/// A lexed string.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StringSegments<'input> {
    Text(Vec<TextSegment<'input>>),
    Interpolated(Vec<InterpolatedSegment<'input>>),
}

impl<'input> StringSegments<'input> {
    fn push_text(&mut self, segment: TextSegment<'input>) {
        match self {
            Self::Text(segments) => segments.push(segment),
            Self::Interpolated(segments) => segments.push(InterpolatedSegment::Text(segment)),
        }
    }

    fn push_interpolated(&mut self, segment: InterpolatedSegment<'input>) {
        match self {
            Self::Text(segments) => {
                *self = Self::Interpolated(
                    segments
                        .drain(..)
                        .map(InterpolatedSegment::Text)
                        .chain(std::iter::once(segment))
                        .collect(),
                );
            }
            Self::Interpolated(segments) => {
                segments.push(segment);
            }
        }
    }
}

/// A lexed string segment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TextSegment<'input> {
    Content(usize, &'input str, usize),
    Escape(usize, char, usize),
}

/// Lexes string segments.
fn lex_string<'input>(
    lex: &mut logos::Lexer<'input, Token<'input>>,
) -> Option<(usize, StringSegments<'input>, usize)> {
    // Remember the opening quote, and the starting position of the string.
    let quote = lex.slice();
    let start = lex.span().start;

    // Switch to the string lexer.
    let mut segments = StringSegments::Text(vec![]);
    let mut string_lex = lex.clone().morph::<StringToken<'input>>();
    while let Some(token) = string_lex.next() {
        match token {
            StringToken::Quote(q) if q == quote => {
                // Matching closing quote; we've reached the end of the string.
                *lex = string_lex.morph::<Token<'input>>();
                return Some((start, segments, lex.span().end));
            }
            StringToken::Content(s) | StringToken::Quote(s) => {
                let Range { start, end } = lex.span();
                segments.push_text(TextSegment::Content(start, s, end));
            }
            StringToken::Escape(c) => {
                let Range { start, end } = lex.span();
                segments.push_text(TextSegment::Escape(start, c, end));
            }
            StringToken::InterpolationStart => {
                // Switch back to the expression lexer for the interpolation.
                let mut expr_lex = string_lex.morph::<Token<'input>>();
                match lex_interpolation(&mut expr_lex) {
                    Some(tokens) => {
                        segments.push_interpolated(InterpolatedSegment::Interpolation(tokens));
                        // Resume lexing the string after the interpolated expression.
                        string_lex = expr_lex.morph::<StringToken<'input>>();
                    }
                    None => {
                        // Error in interpolation.
                        *lex = expr_lex;
                        return None;
                    }
                }
            }
            StringToken::Error => break,
        }
    }

    // Either we reached the end of the input without a closing quote,
    // or the string lexer returned an error.
    *lex = string_lex.morph::<Token<'input>>();
    None
}

/// A lexed interpolated string segment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InterpolatedSegment<'input> {
    Text(TextSegment<'input>),
    Interpolation(Vec<(usize, Token<'input>, usize)>),
}

/// Lexes an interpolated expression in a string,
/// collecting tokens until the matching closing `)`.
fn lex_interpolation<'input>(
    lex: &mut logos::Lexer<'input, Token<'input>>,
) -> Option<Vec<(usize, Token<'input>, usize)>> {
    let mut tokens = vec![];
    let mut depth = 0;
    while let Some(token) = lex.next() {
        match token {
            Token::LeftParen => {
                let Range { start, end } = lex.span();
                depth += 1;
                tokens.push((start, token, end));
            }
            Token::RightParen if depth > 0 => {
                let Range { start, end } = lex.span();
                depth -= 1;
                tokens.push((start, token, end));
            }
            Token::RightParen => {
                // We consumed the opening parenthesis as part of the `\(` token,
                // so a `)` at depth 0 means we've reached the end of the expression.
                return Some(tokens);
            }
            Token::Error => return None,
            token => {
                let Range { start, end } = lex.span();
                tokens.push((start, token, end));
            }
        }
    }
    None
}

/// A lexer for the `jqish` grammar.
///
/// Now uses the `logos` crate with context-dependent lexing via `morph()` for
/// strings and numbers, rather than regular expressions.
pub struct Lexer<'input> {
    inner: logos::Lexer<'input, Token<'input>>,
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Result<(usize, Token<'input>, usize), SpannedError<LexicalError>>;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.inner.next()?;
        let span = self.inner.span();

        match token {
            Token::String((start, segments, end)) => {
                Some(Ok((start, Token::String((start, segments, end)), end)))
            }
            Token::Error => Some(Err(SpannedError {
                error: LexicalError::Unexpected(self.inner.slice().to_owned()),
                location: (span.start, span.end),
            })),
            _ => Some(Ok((span.start, token, span.end))),
        }
    }
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer {
            inner: Token::lexer(input),
        }
    }
}
