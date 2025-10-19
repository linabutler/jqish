// Copyright (c) 2025 Lina Butler
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::{borrow::Cow, fmt::Display, str::FromStr};

use lalrpop_util::ParseError as LalrpopParseError;

use crate::lexer::InterpolatedSegment;

use super::{
    error::{LexicalError, SpannedError},
    lexer::{Lexer, TextSegment},
};

mod grammar {
    // `lalrpop-util` 0.21.0+ supports specifying attributes directly on the generated module,
    // but we're pinned to 0.19.2, which `starlark_syntax` uses. Once Starlark upgrades its
    // `lalrpop` version, we can specify `#![allow(clippy::all)]` directly on the module,
    // and remove this nested module.

    #![allow(clippy::all)]

    use lalrpop_util::lalrpop_mod;

    lalrpop_mod!(grammar, "/jqish.rs");

    pub use grammar::*;
}

/// Parses a string containing a `jq`-like filter expression
/// into an expression tree.
pub fn parse(input: &str) -> Result<Expr<'_>, SpannedError<LexicalError>> {
    let lexer = Lexer::new(input);
    let parser = grammar::TopParser::new();
    parser.parse(lexer).map_err(|err| match err {
        LalrpopParseError::ExtraToken {
            token: (start, _, end),
        } => SpannedError {
            error: LexicalError::BadToken,
            location: (start, end),
        },
        LalrpopParseError::InvalidToken { location: start } => SpannedError {
            error: LexicalError::BadToken,
            location: (start, start + 1),
        },
        LalrpopParseError::UnrecognizedEOF {
            location: start, ..
        } => SpannedError {
            error: LexicalError::BadToken,
            location: (start, start + 1),
        },
        LalrpopParseError::UnrecognizedToken {
            token: (start, _, end),
            ..
        } => SpannedError {
            error: LexicalError::BadToken,
            location: (start, end),
        },
        LalrpopParseError::User { error } => error,
    })
}

/// A segment within an interpolated string.
#[derive(Debug, Clone, PartialEq)]
pub enum InterpolatedStringPart<'a> {
    /// A literal text segment.
    Text(Cow<'a, str>),
    /// An expression to be interpolated.
    Expr(Expr<'a>),
}

/// A `jqish` expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr<'a> {
    /// The identity filter, `.`. This filter takes an input value,
    /// and returns that same value as its output.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// let expr = parse(".").unwrap();
    /// assert_eq!(expr, Expr::Identity);
    /// ```
    Identity,

    /// An integer or floating-point literal.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int, Float}};
    /// let expr = parse("42").unwrap();
    /// assert_eq!(expr, Expr::Number(Int(42).into()));
    ///
    /// let expr = parse("9.42").unwrap();
    /// assert_eq!(expr, Expr::Number(Float(9.42).into()));
    /// ```
    Number(Number),

    /// A single- or double-quoted string literal.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use std::borrow::Cow;
    /// # use jqish::{parse, Expr};
    /// let expr = parse(r#""hello""#).unwrap();
    /// assert_eq!(expr, Expr::String(Cow::Borrowed("hello")));
    ///
    /// let expr = parse("'hello'").unwrap();
    /// assert_eq!(expr, Expr::String(Cow::Borrowed("hello")));
    /// ```
    String(Cow<'a, str>),

    /// An interpolated string with embedded expressions.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use std::borrow::Cow;
    /// # use jqish::{parse, Expr};
    /// let expr = parse(r#""Hello, \(.name + ", how are \("you" + "?")")""#).unwrap();
    /// ```
    InterpolatedString(Vec<InterpolatedStringPart<'a>>),

    /// A Boolean literal.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// let expr = parse("true").unwrap();
    /// assert_eq!(expr, Expr::Bool(true));
    ///
    /// let expr = parse("false").unwrap();
    /// assert_eq!(expr, Expr::Bool(false));
    /// ```
    Bool(bool),

    /// A `null` literal.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// let expr = parse("null").unwrap();
    /// assert_eq!(expr, Expr::Null);
    /// ```
    Null,

    /// An array literal.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("[]").unwrap();
    /// assert_eq!(expr, Expr::Array(vec![]));
    ///
    /// let expr = parse("[1, 2, 3]").unwrap();
    /// assert_eq!(expr, Expr::Array(vec![
    ///     Expr::Number(Int(1).into()),
    ///     Expr::Number(Int(2).into()),
    ///     Expr::Number(Int(3).into()),
    /// ]));
    /// ```
    Array(Vec<Expr<'a>>),

    /// An object literal.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use std::borrow::Cow;
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("{}").unwrap();
    /// assert_eq!(expr, Expr::Object(vec![]));
    ///
    /// let expr = parse("{name, age: 30}").unwrap();
    /// assert_eq!(expr, Expr::Object(vec![
    ///     (Expr::String(Cow::Borrowed("name")), Expr::Index(Expr::Identity.into(), Expr::String(Cow::Borrowed("name")).into())),
    ///     (Expr::String(Cow::Borrowed("age")), Expr::Number(Int(30).into())),
    /// ]));
    /// ```
    Object(Vec<(Expr<'a>, Expr<'a>)>),

    /// A pipe expression, `a | b`. This operator passes the result of `a`
    /// as the input to `b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// # use std::borrow::Cow;
    /// let expr = parse(".user | .name").unwrap();
    /// assert_eq!(expr, Expr::Pipe(
    ///     Expr::Index(
    ///         Expr::Identity.into(),
    ///         Expr::String(Cow::Borrowed("user")).into()
    ///     ).into(),
    ///     Expr::Index(
    ///         Expr::Identity.into(),
    ///         Expr::String(Cow::Borrowed("name")).into()
    ///     ).into()
    /// ));
    /// ```
    Pipe(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A Boolean "or" expression: `a or b`.
    ///
    /// # Example
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// let expr = parse("true or false").unwrap();
    /// assert_eq!(expr, Expr::Or(
    ///     Expr::Bool(true).into(),
    ///     Expr::Bool(false).into()
    /// ));
    /// ```
    Or(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A Boolean "and" expression: `a and b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// let expr = parse("true and false").unwrap();
    /// assert_eq!(expr, Expr::And(
    ///     Expr::Bool(true).into(),
    ///     Expr::Bool(false).into()
    /// ));
    ///
    /// // `and` binds tighter than `or`.
    /// let expr = parse("true and false or null").unwrap();
    /// assert_eq!(expr, Expr::Or(
    ///     Box::new(Expr::And(
    ///         Expr::Bool(true).into(),
    ///         Expr::Bool(false).into()
    ///     )),
    ///     Expr::Null.into()
    /// ));
    /// ```
    And(Box<Expr<'a>>, Box<Expr<'a>>),

    /// An alternative expression, `a // b`. Yields `a` if it's not `false` or `null`,
    /// or `b` otherwise. This is called "null coalescing" in some languages.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// # use std::borrow::Cow;
    /// let expr = parse(".name // 'Unknown'").unwrap();
    /// assert_eq!(expr, Expr::Alt(
    ///     Expr::Index(
    ///         Expr::Identity.into(),
    ///         Expr::String(Cow::Borrowed("name")).into()
    ///     ).into(),
    ///     Expr::String(Cow::Borrowed("Unknown")).into()
    /// ));
    /// ```
    Alt(Box<Expr<'a>>, Box<Expr<'a>>),

    /// An equality expression, `a == b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("1 == 2").unwrap();
    /// assert_eq!(expr, Expr::Equal(
    ///     Expr::Number(Int(1).into()).into(),
    ///     Expr::Number(Int(2).into()).into()
    /// ));
    /// ```
    Equal(Box<Expr<'a>>, Box<Expr<'a>>),

    /// An inequality expression, `a != b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("1 != 2").unwrap();
    /// assert_eq!(expr, Expr::NotEqual(
    ///     Expr::Number(Int(1).into()).into(),
    ///     Expr::Number(Int(2).into()).into()
    /// ));
    /// ```
    NotEqual(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A less-than expression, `a < b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("1 < 2").unwrap();
    /// assert_eq!(expr, Expr::Less(
    ///     Expr::Number(Int(1).into()).into(),
    ///     Expr::Number(Int(2).into()).into()
    /// ));
    /// ```
    Less(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A greater-than expression, `a > b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("1 > 2").unwrap();
    /// assert_eq!(expr, Expr::Greater(
    ///     Expr::Number(Int(1).into()).into(),
    ///     Expr::Number(Int(2).into()).into()
    /// ));
    /// ```
    Greater(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A less-than-or-equal expression, `a <= b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("1 <= 2").unwrap();
    /// assert_eq!(expr, Expr::LessEqual(
    ///     Expr::Number(Int(1).into()).into(),
    ///     Expr::Number(Int(2).into()).into()
    /// ));
    /// ```
    LessEqual(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A greater-than-or-equal expression, `a >= b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("1 >= 2").unwrap();
    /// assert_eq!(expr, Expr::GreaterEqual(
    ///     Expr::Number(Int(1).into()).into(),
    ///     Expr::Number(Int(2).into()).into()
    /// ));
    /// ```
    GreaterEqual(Box<Expr<'a>>, Box<Expr<'a>>),

    /// An addition expression, `a + b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("1 + 2").unwrap();
    /// assert_eq!(expr, Expr::Add(
    ///     Expr::Number(Int(1).into()).into(),
    ///     Expr::Number(Int(2).into()).into()
    /// ));
    /// ```
    Add(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A subtraction expression, `a - b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("1 - 2").unwrap();
    /// assert_eq!(expr, Expr::Subtract(
    ///     Expr::Number(Int(1).into()).into(),
    ///     Expr::Number(Int(2).into()).into()
    /// ));
    /// ```
    Subtract(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A multiplication expression, `a * b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("1 * 2").unwrap();
    /// assert_eq!(expr, Expr::Multiply(
    ///     Expr::Number(Int(1).into()).into(),
    ///     Expr::Number(Int(2).into()).into()
    /// ));
    /// ```
    Multiply(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A division expression, `a / b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("1 / 2").unwrap();
    /// assert_eq!(expr, Expr::Divide(
    ///     Expr::Number(Int(1).into()).into(),
    ///     Expr::Number(Int(2).into()).into()
    /// ));
    /// ```
    Divide(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A modulo expression, `a % b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("1 % 2").unwrap();
    /// assert_eq!(expr, Expr::Modulo(
    ///     Expr::Number(Int(1).into()).into(),
    ///     Expr::Number(Int(2).into()).into()
    /// ));
    /// ```
    Modulo(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A negated expression, `-a`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse("-42").unwrap();
    /// assert_eq!(expr, Expr::Negate(Expr::Number(Int(42).into()).into()));
    /// ```
    Negate(Box<Expr<'a>>),

    /// A Boolean "not" expression, `not a`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// let expr = parse("not true").unwrap();
    /// assert_eq!(expr, Expr::Not(Expr::Bool(true).into()));
    ///
    /// // `not` binds tighter than `and` or `or`.
    /// let expr = parse("not true and false").unwrap();
    /// assert_eq!(expr, Expr::And(
    ///     Expr::Not(Expr::Bool(true).into()).into(),
    ///     Expr::Bool(false).into()
    /// ));
    /// ```
    Not(Box<Expr<'a>>),

    /// An optional expression, `expr?`, which short-circuits to `null` if
    /// `expr` is `null` or an error. This is sometimes called the
    /// "safe navigation operator" in other languages.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// # use std::borrow::Cow;
    /// let expr = parse(".name?").unwrap();
    /// assert_eq!(expr, Expr::Opt(
    ///     Expr::Index(
    ///         Expr::Identity.into(),
    ///         Expr::String(Cow::Borrowed("name")).into(),
    ///     ).into()
    /// ));
    /// ```
    Opt(Box<Expr<'a>>),

    /// An indexing operation, `.[expr]`, used to access
    /// array elements and object properties.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// # use std::borrow::Cow;
    /// let expr = parse(".[0]").unwrap();
    /// assert_eq!(expr, Expr::Index(
    ///     Expr::Identity.into(),
    ///     Expr::Number(Int(0).into()).into()
    /// ));
    ///
    /// let expr = parse(".name").unwrap();
    /// assert_eq!(expr, Expr::Index(
    ///     Expr::Identity.into(),
    ///     Expr::String(Cow::Borrowed("name")).into()
    /// ));
    /// ```
    Index(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A slice expression, `.[start:end]`. Both `start` and `end` are optional,
    /// and respectively default to the beginning and end of the array if omitted.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::{Number, Int}};
    /// let expr = parse(".[1:3]").unwrap();
    /// assert_eq!(expr, Expr::Slice(
    ///     Expr::Identity.into(),
    ///     Some(Expr::Number(Int(1).into()).into()),
    ///     Some(Expr::Number(Int(3).into()).into())
    /// ));
    ///
    /// let expr = parse(".[2:]").unwrap();
    /// assert_eq!(expr, Expr::Slice(
    ///     Expr::Identity.into(),
    ///     Some(Expr::Number(Int(2).into()).into()),
    ///     None
    /// ));
    ///
    /// let expr = parse(".[:5]").unwrap();
    /// assert_eq!(expr, Expr::Slice(
    ///     Expr::Identity.into(),
    ///     None,
    ///     Some(Expr::Number(Int(5).into()).into())
    /// ));
    /// ```
    Slice(Box<Expr<'a>>, Option<Box<Expr<'a>>>, Option<Box<Expr<'a>>>),

    /// A function call expression, like `name()`, `name(arg)`, or
    /// `name(arg1; arg2; arg3)`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// # use std::borrow::Cow;
    /// let expr = parse("length()").unwrap();
    /// assert_eq!(expr, Expr::Call("length", vec![]));
    ///
    /// let expr = parse("map(.name)").unwrap();
    /// assert_eq!(expr, Expr::Call("map", vec![
    ///     Expr::Index(
    ///         Expr::Identity.into(),
    ///         Expr::String(Cow::Borrowed("name")).into(),
    ///     ),
    /// ]));
    /// ```
    Call(&'a str, Vec<Expr<'a>>),

    /// A block with a variable declaration and a following expression,
    /// `expr as $name | expr` or `expr as pattern | expr`.
    Block(Pattern<'a>, Box<Expr<'a>>, Box<Expr<'a>>),

    /// A variable binding, `$name`.
    Binding(&'a str),
}

/// A pattern for destructuring assignment.
#[derive(Debug, Clone, PartialEq)]
pub enum Pattern<'a> {
    /// A simple variable binding, `$name`.
    Variable(&'a str),

    /// Array destructuring pattern, `[$first, $second, ...]`.
    Array(Vec<Pattern<'a>>),

    /// Object destructuring pattern, `{key1: $var1, key2: $var2, ...}`.
    Object(Vec<(Expr<'a>, Pattern<'a>)>),

    /// Alternative patterns, `pat1 ?// pat2 ?// pat3`.
    /// If the first pattern fails to match, try the next one.
    Alternative(Box<Pattern<'a>>, Box<Pattern<'a>>),
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Int(pub i64);

impl Display for Int {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl FromStr for Int {
    type Err = NumberError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse().map(Self).map_err(|_| Self::Err::Int)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct Float(pub f64);

impl Display for Float {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl FromStr for Float {
    type Err = NumberError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse().map(Self).map_err(|_| Self::Err::Float)
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Number {
    Int(Int),
    Float(Float),
}

impl From<Int> for Number {
    fn from(value: Int) -> Self {
        Self::Int(value)
    }
}

impl From<Float> for Number {
    fn from(value: Float) -> Self {
        Self::Float(value)
    }
}

impl FromStr for Number {
    type Err = NumberError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse()
            .map(Self::Int)
            .or_else(|_| s.parse().map(Self::Float))
            .map_err(|_| Self::Err::Number)
    }
}

#[derive(Debug, thiserror::Error)]
pub enum BadInterpolationError {
    #[error(transparent)]
    Escape(#[from] SpannedError<BadEscapeError>),

    #[error(transparent)]
    Lexical(#[from] SpannedError<LexicalError>),
}

pub fn interpolate<'input>(
    segments: Vec<InterpolatedSegment<'input>>,
) -> Result<Vec<InterpolatedStringPart<'input>>, BadInterpolationError> {
    let segments = segments
        .into_iter()
        .map(|segment| match segment {
            InterpolatedSegment::Text(text) => Ok(InterpolatedStringPart::Text(unquote(
                std::slice::from_ref(&text),
            )?)),
            InterpolatedSegment::Interpolation(tokens) => {
                let expr = grammar::TopParser::new()
                    .parse(tokens)
                    .map_err(|err| match err {
                        LalrpopParseError::ExtraToken {
                            token: (start, _, end),
                        } => SpannedError {
                            error: LexicalError::BadToken,
                            location: (start, end),
                        },
                        LalrpopParseError::InvalidToken { location: start } => SpannedError {
                            error: LexicalError::BadToken,
                            location: (start, start),
                        },
                        LalrpopParseError::UnrecognizedEOF {
                            location: start, ..
                        } => SpannedError {
                            error: LexicalError::BadToken,
                            location: (start, start + 1),
                        },
                        LalrpopParseError::UnrecognizedToken {
                            token: (start, _, end),
                            ..
                        } => SpannedError {
                            error: LexicalError::BadToken,
                            location: (start, end),
                        },
                        LalrpopParseError::User { error } => error,
                    })?;
                Ok(InterpolatedStringPart::Expr(expr))
            }
        })
        .collect::<Result<_, BadInterpolationError>>()?;

    Ok(segments)
}

/// Removes surrounding quotes from, and expands escape sequences in,
/// a string literal.
pub fn unquote<'input>(
    segments: &[TextSegment<'input>],
) -> Result<Cow<'input, str>, SpannedError<BadEscapeError>> {
    if let &[TextSegment::Content(_, content, _)] = segments {
        // If the string doesn't contain any escape sequences,
        // we can just drop the surrounding quotes and
        // return the contents.
        return Ok(Cow::Borrowed(content));
    }
    let mut string = String::new();
    for s in segments {
        match s {
            TextSegment::Content(_, s, _) => string.push_str(s),
            TextSegment::Escape(_, 'n', _) => string.push('\n'),
            TextSegment::Escape(_, 'r', _) => string.push('\r'),
            TextSegment::Escape(_, 't', _) => string.push('\t'),
            &TextSegment::Escape(_, c @ ('"' | '\'' | '\\'), _) => string.push(c),
            &TextSegment::Escape(start, c, end) => Err(SpannedError {
                error: BadEscapeError(c),
                location: (start, end),
            })?,
        }
    }
    Ok(Cow::Owned(string))
}

#[derive(Debug, thiserror::Error)]
#[error("unsupported escape sequence `\\{0}`")]
pub struct BadEscapeError(char);

#[derive(Debug, thiserror::Error)]
pub enum NumberError {
    #[error("can't parse this value as an integer")]
    Int,
    #[error("can't parse this value as a float")]
    Float,
    #[error("can't parse this value as a number")]
    Number,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_identity() {
        let result = parse(".").unwrap();
        assert_eq!(result, Expr::Identity);
    }

    #[test]
    fn test_parse_number() {
        let result = parse("42").unwrap();
        assert_eq!(result, Expr::Number(Int(42).into()));
    }

    #[test]
    fn test_parse_string() {
        let result = parse(r#""hello""#).unwrap();
        assert_eq!(result, Expr::String("hello".into()));
    }

    #[test]
    fn test_parse_field_access() {
        let result = parse(".foo").unwrap();
        assert_eq!(
            result,
            Expr::Index(Expr::Identity.into(), Expr::String("foo".into()).into())
        );
    }

    #[test]
    fn test_parse_pipe() {
        let result = parse(". | .foo").unwrap();
        assert_eq!(
            result,
            Expr::Pipe(
                Expr::Identity.into(),
                Expr::Index(Expr::Identity.into(), Expr::String("foo".into()).into()).into()
            )
        );
    }

    #[test]
    fn test_simple_chained_access() {
        let result = parse(".user.name").unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into()).into(),
                Expr::String("name".into()).into()
            )
        );
    }

    #[test]
    fn test_object_with_optional_nested_properties() {
        let result = parse(
            r#"{status: .status, error: .body.error?, apps: .body.data?.project.supportedApps?}"#,
        )
        .unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("status".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("status".into()).into(),)
                ),
                (
                    Expr::String("error".into()),
                    Expr::Opt(
                        Expr::Index(
                            Expr::Index(Expr::Identity.into(), Expr::String("body".into()).into(),)
                                .into(),
                            Expr::String("error".into()).into()
                        )
                        .into()
                    ),
                ),
                (
                    Expr::String("apps".into()),
                    Expr::Opt(
                        Expr::Index(
                            Expr::Index(
                                Expr::Opt(
                                    Expr::Index(
                                        Expr::Index(
                                            Expr::Identity.into(),
                                            Expr::String("body".into()).into(),
                                        )
                                        .into(),
                                        Expr::String("data".into()).into(),
                                    )
                                    .into()
                                )
                                .into(),
                                Expr::String("project".into()).into(),
                            )
                            .into(),
                            Expr::String("supportedApps".into()).into()
                        )
                        .into()
                    )
                )
            ])
        );
    }

    #[test]
    fn test_chained_access_in_pipe() {
        let result = parse(".response.data | .user.name").unwrap();
        assert_eq!(
            result,
            Expr::Pipe(
                Expr::Index(
                    Expr::Index(
                        Expr::Identity.into(),
                        Expr::String("response".into()).into()
                    )
                    .into(),
                    Expr::String("data".into()).into()
                )
                .into(),
                Expr::Index(
                    Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into()).into(),
                    Expr::String("name".into()).into()
                )
                .into(),
            )
        );
    }

    #[test]
    fn test_object_with_complex_values() {
        let result = parse(r#"{result: contains("string"), count: length()}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("result".into()),
                    Expr::Call("contains", vec![Expr::String("string".into())]),
                ),
                (Expr::String("count".into()), Expr::Call("length", vec![]),)
            ])
        );
    }

    #[test]
    fn test_arithmetic() {
        let result = parse("-6. - 1. >= 5").unwrap();
        assert_eq!(
            result,
            Expr::GreaterEqual(
                Expr::Subtract(
                    Expr::Negate(Expr::Number(Float(6.0).into()).into()).into(),
                    Expr::Number(Float(1.0).into()).into()
                )
                .into(),
                Expr::Number(Int(5).into()).into()
            )
        );
    }

    #[test]
    fn test_escapes() {
        let result = parse(r#""a\"b""#).unwrap();
        assert_eq!(result, Expr::String(r#"a"b"#.into()));
    }

    #[test]
    fn test_alternative() {
        let result =
            parse(r#"(.username or true and false // .user and false or true // "not available")"#)
                .unwrap();
        assert_eq!(
            result,
            Expr::Alt(
                Expr::Alt(
                    Expr::Or(
                        Expr::Index(
                            Expr::Identity.into(),
                            Expr::String("username".into()).into()
                        )
                        .into(),
                        Expr::And(Expr::Bool(true).into(), Expr::Bool(false).into()).into(),
                    )
                    .into(),
                    Expr::Or(
                        Expr::And(
                            Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into())
                                .into(),
                            Expr::Bool(false).into()
                        )
                        .into(),
                        Expr::Bool(true).into()
                    )
                    .into(),
                )
                .into(),
                Expr::String("not available".into()).into()
            )
        );
    }

    #[test]
    fn test_slice_expressions() {
        let result = parse(".[1:3]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Expr::Identity.into(),
                Some(Expr::Number(Int(1).into()).into()),
                Some(Expr::Number(Int(3).into()).into())
            )
        );

        let result = parse(".[2:]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Expr::Identity.into(),
                Some(Expr::Number(Int(2).into()).into()),
                None
            )
        );

        let result = parse(".[:5]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Expr::Identity.into(),
                None,
                Some(Expr::Number(Int(5).into()).into())
            )
        );

        let result = parse(".[:]").unwrap();
        assert_eq!(result, Expr::Slice(Expr::Identity.into(), None, None));
    }

    #[test]
    fn test_chained_slice_expressions() {
        let result = parse(".data[1:3]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Expr::Index(Expr::Identity.into(), Expr::String("data".into()).into()).into(),
                Some(Expr::Number(Int(1).into()).into()),
                Some(Expr::Number(Int(3).into()).into())
            )
        );

        let result = parse(".[length() - 2:]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Expr::Identity.into(),
                Some(
                    Expr::Subtract(
                        Expr::Call("length", vec![]).into(),
                        Expr::Number(Int(2).into()).into()
                    )
                    .into()
                ),
                None
            )
        );
    }

    #[test]
    fn test_comprehensive_operators() {
        let result = parse("1 + 2 * 3 - 4 / 5 % 6").unwrap();
        assert_eq!(
            result,
            Expr::Subtract(
                Expr::Add(
                    Expr::Number(Int(1).into()).into(),
                    Expr::Multiply(
                        Expr::Number(Int(2).into()).into(),
                        Expr::Number(Int(3).into()).into()
                    )
                    .into()
                )
                .into(),
                Expr::Modulo(
                    Expr::Divide(
                        Expr::Number(Int(4).into()).into(),
                        Expr::Number(Int(5).into()).into()
                    )
                    .into(),
                    Expr::Number(Int(6).into()).into()
                )
                .into()
            )
        );

        let _result = parse("1 < 2 <= 3 > 4 >= 5 == 6 != 7").unwrap();

        let result = parse("true and false or null").unwrap();
        assert_eq!(
            result,
            Expr::Or(
                Expr::And(Expr::Bool(true).into(), Expr::Bool(false).into()).into(),
                Expr::Null.into()
            )
        );
    }

    #[test]
    fn test_complex_field_access() {
        let result = parse(".user.profile.settings.theme").unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Expr::Index(
                    Expr::Index(
                        Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into())
                            .into(),
                        Expr::String("profile".into()).into()
                    )
                    .into(),
                    Expr::String("settings".into()).into()
                )
                .into(),
                Expr::String("theme".into()).into()
            )
        );

        let result = parse(".user?.profile.settings?.theme?").unwrap();
        assert_eq!(
            result,
            Expr::Opt(
                Expr::Index(
                    Expr::Opt(
                        Expr::Index(
                            Expr::Index(
                                Expr::Opt(
                                    Expr::Index(
                                        Expr::Identity.into(),
                                        Expr::String("user".into()).into()
                                    )
                                    .into()
                                )
                                .into(),
                                Expr::String("profile".into()).into()
                            )
                            .into(),
                            Expr::String("settings".into()).into()
                        )
                        .into()
                    )
                    .into(),
                    Expr::String("theme".into()).into()
                )
                .into()
            )
        );
    }

    #[test]
    fn test_comprehensive_indexing() {
        let result = parse(".[0][1][2]").unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Expr::Index(
                    Expr::Index(Expr::Identity.into(), Expr::Number(Int(0).into()).into()).into(),
                    Expr::Number(Int(1).into()).into()
                )
                .into(),
                Expr::Number(Int(2).into()).into()
            )
        );

        let result = parse(".users[0].name[0:3]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Expr::Index(
                    Expr::Index(
                        Expr::Index(Expr::Identity.into(), Expr::String("users".into()).into())
                            .into(),
                        Expr::Number(Int(0).into()).into()
                    )
                    .into(),
                    Expr::String("name".into()).into()
                )
                .into(),
                Some(Expr::Number(Int(0).into()).into()),
                Some(Expr::Number(Int(3).into()).into())
            )
        );

        let result = parse(".[0]?[1]?.field?").unwrap();
        assert_eq!(
            result,
            Expr::Opt(
                Expr::Index(
                    Expr::Opt(
                        Expr::Index(
                            Expr::Opt(
                                Expr::Index(
                                    Expr::Identity.into(),
                                    Expr::Number(Int(0).into()).into()
                                )
                                .into()
                            )
                            .into(),
                            Expr::Number(Int(1).into()).into()
                        )
                        .into()
                    )
                    .into(),
                    Expr::String("field".into()).into()
                )
                .into()
            )
        );
    }

    #[test]
    fn test_comprehensive_slicing() {
        let test_cases = vec![
            (".[:]", Expr::Slice(Expr::Identity.into(), None, None)),
            (
                ".[1:]",
                Expr::Slice(
                    Expr::Identity.into(),
                    Some(Expr::Number(Int(1).into()).into()),
                    None,
                ),
            ),
            (
                ".[:5]",
                Expr::Slice(
                    Expr::Identity.into(),
                    None,
                    Some(Expr::Number(Int(5).into()).into()),
                ),
            ),
            (
                ".[1:5]",
                Expr::Slice(
                    Expr::Identity.into(),
                    Some(Expr::Number(Int(1).into()).into()),
                    Some(Expr::Number(Int(5).into()).into()),
                ),
            ),
        ];

        for (input, expected) in test_cases {
            let result = parse(input).unwrap();
            assert_eq!(result, expected, "Failed for input: {}", input);
        }

        let result = parse(".[length() - 1:length()]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Expr::Identity.into(),
                Some(
                    Expr::Subtract(
                        Expr::Call("length", vec![]).into(),
                        Expr::Number(Int(1).into()).into()
                    )
                    .into()
                ),
                Some(Expr::Call("length", vec![]).into())
            )
        );
    }

    #[test]
    fn test_function_calls() {
        let result = parse("length()").unwrap();
        assert_eq!(result, Expr::Call("length", vec![]));

        let result = parse("map(.name; .age)").unwrap();
        assert_eq!(
            result,
            Expr::Call(
                "map",
                vec![
                    Expr::Index(Expr::Identity.into(), Expr::String("name".into()).into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("age".into()).into())
                ]
            )
        );

        let result = parse("sort_by(length(.name))").unwrap();
        assert_eq!(
            result,
            Expr::Call(
                "sort_by",
                vec![Expr::Call(
                    "length",
                    vec![Expr::Index(
                        Expr::Identity.into(),
                        Expr::String("name".into()).into()
                    )]
                )]
            )
        );
    }

    #[test]
    fn test_complex_objects() {
        let result =
            parse(r#"{name: .user, "full name": .user.full_name, (."key-with-dashes"): .value}"#)
                .unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("name".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into())
                ),
                (
                    Expr::String("full name".into()),
                    Expr::Index(
                        Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into())
                            .into(),
                        Expr::String("full_name".into()).into(),
                    )
                ),
                (
                    Expr::Index(
                        Expr::Identity.into(),
                        Expr::String("key-with-dashes".into()).into()
                    ),
                    Expr::Index(Expr::Identity.into(), Expr::String("value".into()).into())
                )
            ])
        );

        let result = parse("{}").unwrap();
        assert_eq!(result, Expr::Object(vec![]));

        let result = parse(r#"{user: {name: .name, age: .age}, active: true}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("user".into()),
                    Expr::Object(vec![
                        (
                            Expr::String("name".into()),
                            Expr::Index(Expr::Identity.into(), Expr::String("name".into()).into())
                        ),
                        (
                            Expr::String("age".into()),
                            Expr::Index(Expr::Identity.into(), Expr::String("age".into()).into())
                        )
                    ])
                ),
                (Expr::String("active".into()), Expr::Bool(true))
            ])
        );
    }

    #[test]
    fn test_complex_arrays() {
        let result = parse("[.name, .age + 1, length(.items), {status: .active}]").unwrap();
        assert_eq!(
            result,
            Expr::Array(vec![
                Expr::Index(Expr::Identity.into(), Expr::String("name".into()).into()),
                Expr::Add(
                    Expr::Index(Expr::Identity.into(), Expr::String("age".into()).into()).into(),
                    Expr::Number(Int(1).into()).into()
                ),
                Expr::Call(
                    "length",
                    vec![Expr::Index(
                        Expr::Identity.into(),
                        Expr::String("items".into()).into()
                    )]
                ),
                Expr::Object(vec![(
                    Expr::String("status".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("active".into()).into())
                )])
            ])
        );

        let result = parse("[]").unwrap();
        assert_eq!(result, Expr::Array(vec![]));

        let result = parse("[[1, 2], [3, 4]]").unwrap();
        assert_eq!(
            result,
            Expr::Array(vec![
                Expr::Array(vec![
                    Expr::Number(Int(1).into()),
                    Expr::Number(Int(2).into())
                ]),
                Expr::Array(vec![
                    Expr::Number(Int(3).into()),
                    Expr::Number(Int(4).into())
                ])
            ])
        );
    }

    #[test]
    fn test_complex_pipes() {
        let result = parse(".users | map(.name) | sort() | .[0:5]").unwrap();
        assert_eq!(
            result,
            Expr::Pipe(
                Expr::Pipe(
                    Expr::Pipe(
                        Expr::Index(Expr::Identity.into(), Expr::String("users".into()).into())
                            .into(),
                        Expr::Call(
                            "map",
                            vec![Expr::Index(
                                Expr::Identity.into(),
                                Expr::String("name".into()).into()
                            )]
                        )
                        .into()
                    )
                    .into(),
                    Expr::Call("sort", vec![]).into()
                )
                .into(),
                Expr::Slice(
                    Expr::Identity.into(),
                    Some(Expr::Number(Int(0).into()).into()),
                    Some(Expr::Number(Int(5).into()).into())
                )
                .into()
            )
        );

        let result = parse(".name // \"Unknown\" | length()").unwrap();
        assert_eq!(
            result,
            Expr::Pipe(
                Expr::Alt(
                    Expr::Index(Expr::Identity.into(), Expr::String("name".into()).into()).into(),
                    Expr::String("Unknown".into()).into()
                )
                .into(),
                Expr::Call("length", vec![]).into()
            )
        );
    }

    #[test]
    fn test_string_escapes() {
        let test_cases = vec![
            (r#""hello""#, "hello"),
            (r#""hello\nworld""#, "hello\nworld"),
            (r#""say \"hi\"""#, "say \"hi\""),
            (r#""path\\to\\file""#, "path\\to\\file"),
            (r#""tab\there""#, "tab\there"),
            (r#""return\r""#, "return\r"),
        ];

        for (input, expected) in test_cases {
            let result = parse(input).unwrap();
            assert_eq!(
                result,
                Expr::String(expected.into()),
                "Failed for input: {}",
                input
            );
        }
    }

    #[test]
    fn test_number_formats() {
        let positive_cases = vec![
            ("42", Expr::Number(Int(42).into())),
            ("9.42", Expr::Number(Float(9.42).into())),
            ("0", Expr::Number(Int(0).into())),
            ("0.5", Expr::Number(Float(0.5).into())),
            (".5", Expr::Number(Float(0.5).into())),
            ("1e10", Expr::Number(Float(1e10).into())),
        ];

        for (input, expected) in positive_cases {
            let actual = parse(input).unwrap();
            assert_eq!(actual, expected, "Failed for input: {}", input);
        }

        let result = parse("-7").unwrap();
        assert_eq!(result, Expr::Negate(Expr::Number(Int(7).into()).into()));

        let result = parse("-9.42").unwrap();
        assert_eq!(
            result,
            Expr::Negate(Expr::Number(Float(9.42).into()).into())
        );

        let result = parse("1.5e-3").unwrap();
        assert_eq!(result, Expr::Number(Float(1.5e-3).into()));
    }

    #[test]
    fn test_precedence() {
        let result = parse("1 + 2 * 3").unwrap();
        assert_eq!(
            result,
            Expr::Add(
                Expr::Number(Int(1).into()).into(),
                Expr::Multiply(
                    Expr::Number(Int(2).into()).into(),
                    Expr::Number(Int(3).into()).into()
                )
                .into()
            )
        );

        let result = parse("(1 + 2) * 3").unwrap();
        assert_eq!(
            result,
            Expr::Multiply(
                Expr::Add(
                    Expr::Number(Int(1).into()).into(),
                    Expr::Number(Int(2).into()).into()
                )
                .into(),
                Expr::Number(Int(3).into()).into()
            )
        );

        let result = parse(".user.age + 1").unwrap();
        assert_eq!(
            result,
            Expr::Add(
                Expr::Index(
                    Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into()).into(),
                    Expr::String("age".into()).into()
                )
                .into(),
                Expr::Number(Int(1).into()).into()
            )
        );
    }

    #[test]
    fn test_error_cases() {
        let error_cases = vec![
            "[1,]",         // Trailing comma in array
            ".foo.",        // Trailing dot
            "1 +",          // Incomplete expression
            "func(",        // Unclosed function call
            r#""unclosed"#, // Unclosed string
        ];

        for input in error_cases {
            let result = parse(input);
            assert!(result.is_err(), "Expected error for input: {}", input);
        }
    }

    #[test]
    fn test_whitespace_handling() {
        let test_cases = vec![
            (".foo", ".  foo"),
            (".foo.bar", ".foo  .  bar"),
            ("1 + 2", "1+2"),
            ("{a: 1, b: 2}", "{ a : 1 , b : 2 }"),
            ("[1, 2, 3]", "[ 1 , 2 , 3 ]"),
        ];

        for (compact, spaced) in test_cases {
            let result1 = parse(compact).unwrap();
            let result2 = parse(spaced).unwrap();
            assert_eq!(
                result1, result2,
                "Whitespace handling failed for: {} vs {}",
                compact, spaced
            );
        }
    }

    #[test]
    fn test_quoted_key_field_access() {
        let result = parse(r#"."field-with-dashes""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Expr::Identity.into(),
                Expr::String("field-with-dashes".into()).into()
            )
        );

        let result = parse(r#"."field with spaces""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Expr::Identity.into(),
                Expr::String("field with spaces".into()).into()
            )
        );

        let result = parse(r#"."%@#$^&*()""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Expr::Identity.into(),
                Expr::String("%@#$^&*()".into()).into()
            )
        );

        let result = parse(r#"."field-with-dashes"?"#).unwrap();
        assert_eq!(
            result,
            Expr::Opt(
                Expr::Index(
                    Expr::Identity.into(),
                    Expr::String("field-with-dashes".into()).into()
                )
                .into()
            )
        );

        let result = parse(r#".user"#).unwrap(); // This works
        assert_eq!(
            result,
            Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into())
        );
    }

    #[test]
    fn test_quoted_keys_in_objects() {
        let result = parse(r#"{"field-with-dashes": .value, "spaces in key": .other}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("field-with-dashes".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("value".into()).into())
                ),
                (
                    Expr::String("spaces in key".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("other".into()).into())
                )
            ])
        );

        let result = parse(r#"{true: .yes, false: .no, null: .empty}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::Bool(true),
                    Expr::Index(Expr::Identity.into(), Expr::String("yes".into()).into())
                ),
                (
                    Expr::Bool(false),
                    Expr::Index(Expr::Identity.into(), Expr::String("no".into()).into())
                ),
                (
                    Expr::Null,
                    Expr::Index(Expr::Identity.into(), Expr::String("empty".into()).into())
                )
            ])
        );

        let result = parse(r#"{name: .user, "full-name": .user.name, true: .active}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("name".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into())
                ),
                (
                    Expr::String("full-name".into()),
                    Expr::Index(
                        Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into())
                            .into(),
                        Expr::String("name".into()).into()
                    )
                ),
                (
                    Expr::Bool(true),
                    Expr::Index(Expr::Identity.into(), Expr::String("active".into()).into())
                )
            ])
        );
    }

    #[test]
    fn test_boolean_and_null_literal_field_access() {
        let result = parse(".true").unwrap();
        assert_eq!(
            result,
            Expr::Index(Expr::Identity.into(), Expr::Bool(true).into())
        );

        let result = parse(".false").unwrap();
        assert_eq!(
            result,
            Expr::Index(Expr::Identity.into(), Expr::Bool(false).into())
        );

        let result = parse(".null").unwrap();
        assert_eq!(
            result,
            Expr::Index(Expr::Identity.into(), Expr::Null.into())
        );

        let result = parse(".data.true").unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Expr::Index(Expr::Identity.into(), Expr::String("data".into()).into()).into(),
                Expr::Bool(true).into()
            )
        );

        let result = parse(".config.false.enabled").unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Expr::Index(
                    Expr::Index(Expr::Identity.into(), Expr::String("config".into()).into()).into(),
                    Expr::Bool(false).into()
                )
                .into(),
                Expr::String("enabled".into()).into()
            )
        );

        let result = parse(".data.null?").unwrap();
        assert_eq!(
            result,
            Expr::Opt(
                Expr::Index(
                    Expr::Index(Expr::Identity.into(), Expr::String("data".into()).into()).into(),
                    Expr::Null.into()
                )
                .into()
            )
        );

        let result = parse(r#"{true: .yes, false: .no, null: .empty}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::Bool(true),
                    Expr::Index(Expr::Identity.into(), Expr::String("yes".into()).into())
                ),
                (
                    Expr::Bool(false),
                    Expr::Index(Expr::Identity.into(), Expr::String("no".into()).into())
                ),
                (
                    Expr::Null,
                    Expr::Index(Expr::Identity.into(), Expr::String("empty".into()).into())
                )
            ])
        );
    }

    #[test]
    fn test_expression_as_object_key() {
        let result = parse("{ (.response.data): 123 }").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![(
                Expr::Index(
                    Expr::Index(
                        Expr::Identity.into(),
                        Expr::String("response".into()).into()
                    )
                    .into(),
                    Expr::String("data".into()).into()
                ),
                Expr::Number(Int(123).into())
            )])
        );

        let result = parse("{ (.key1): .value1, (.key2): .value2 }").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::Index(Expr::Identity.into(), Expr::String("key1".into()).into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("value1".into()).into())
                ),
                (
                    Expr::Index(Expr::Identity.into(), Expr::String("key2".into()).into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("value2".into()).into())
                )
            ])
        );

        let result = parse(r#"{ (.prefix + "-" + .suffix): .result }"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![(
                Expr::Add(
                    Expr::Add(
                        Expr::Index(Expr::Identity.into(), Expr::String("prefix".into()).into())
                            .into(),
                        Expr::String("-".into()).into()
                    )
                    .into(),
                    Expr::Index(Expr::Identity.into(), Expr::String("suffix".into()).into()).into()
                ),
                Expr::Index(Expr::Identity.into(), Expr::String("result".into()).into())
            )])
        );
    }

    #[test]
    fn test_chained_quoted_key_access() {
        let result = parse(r#".data."field-name""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Expr::Index(Expr::Identity.into(), Expr::String("data".into()).into()).into(),
                Expr::String("field-name".into()).into()
            )
        );

        let result = parse(r#".user."full-name".display"#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Expr::Index(
                    Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into()).into(),
                    Expr::String("full-name".into()).into()
                )
                .into(),
                Expr::String("display".into()).into()
            )
        );

        let result = parse(r#".data."field-name"?"#).unwrap();
        assert_eq!(
            result,
            Expr::Opt(
                Expr::Index(
                    Expr::Index(Expr::Identity.into(), Expr::String("data".into()).into()).into(),
                    Expr::String("field-name".into()).into()
                )
                .into()
            )
        );

        let result = parse(r#".response."api-data"."user-info"."email-address""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Expr::Index(
                    Expr::Index(
                        Expr::Index(
                            Expr::Identity.into(),
                            Expr::String("response".into()).into()
                        )
                        .into(),
                        Expr::String("api-data".into()).into()
                    )
                    .into(),
                    Expr::String("user-info".into()).into()
                )
                .into(),
                Expr::String("email-address".into()).into()
            )
        );
    }

    #[test]
    fn test_edge_cases_quoted_keys() {
        let result = parse(r#"."""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(Expr::Identity.into(), Expr::String("".into()).into())
        );

        let result = parse(r#"."\n\t\r""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(Expr::Identity.into(), Expr::String("\n\t\r".into()).into())
        );

        let result = parse(r#"."123""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(Expr::Identity.into(), Expr::String("123".into()).into())
        );

        let result = parse(r#".">>=""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(Expr::Identity.into(), Expr::String(">>=".into()).into())
        );

        let result = parse(r#"{"true": .value}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![(
                Expr::String("true".into()),
                Expr::Index(Expr::Identity.into(), Expr::String("value".into()).into())
            )])
        );
    }

    #[test]
    fn test_comprehensive_quoted_key_features() {
        let result = parse(r#".api."user-data".profile.true."last-login".false"#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Expr::Index(
                    Expr::Index(
                        Expr::Index(
                            Expr::Index(
                                Expr::Index(
                                    Expr::Identity.into(),
                                    Expr::String("api".into()).into()
                                )
                                .into(),
                                Expr::String("user-data".into()).into()
                            )
                            .into(),
                            Expr::String("profile".into()).into()
                        )
                        .into(),
                        Expr::Bool(true).into()
                    )
                    .into(),
                    Expr::String("last-login".into()).into()
                )
                .into(),
                Expr::Bool(false).into()
            )
        );

        let result = parse(
            r#"{
            name: .user,
            "full-name": .user."display-name",
            true: .settings.enabled,
            false: .settings.disabled,
            null: .empty,
            (.computed): .dynamic
        }"#,
        )
        .unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("name".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into())
                ),
                (
                    Expr::String("full-name".into()),
                    Expr::Index(
                        Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into())
                            .into(),
                        Expr::String("display-name".into()).into()
                    )
                ),
                (
                    Expr::Bool(true),
                    Expr::Index(
                        Expr::Index(
                            Expr::Identity.into(),
                            Expr::String("settings".into()).into()
                        )
                        .into(),
                        Expr::String("enabled".into()).into()
                    )
                ),
                (
                    Expr::Bool(false),
                    Expr::Index(
                        Expr::Index(
                            Expr::Identity.into(),
                            Expr::String("settings".into()).into()
                        )
                        .into(),
                        Expr::String("disabled".into()).into()
                    )
                ),
                (
                    Expr::Null,
                    Expr::Index(Expr::Identity.into(), Expr::String("empty".into()).into())
                ),
                (
                    Expr::Index(
                        Expr::Identity.into(),
                        Expr::String("computed".into()).into()
                    ),
                    Expr::Index(Expr::Identity.into(), Expr::String("dynamic".into()).into())
                )
            ])
        );

        let result = parse(r#".data."user-info"?.true."settings"?.null?"#).unwrap();
        assert_eq!(
            result,
            Expr::Opt(
                Expr::Index(
                    Expr::Opt(
                        Expr::Index(
                            Expr::Index(
                                Expr::Opt(
                                    Expr::Index(
                                        Expr::Index(
                                            Expr::Identity.into(),
                                            Expr::String("data".into()).into()
                                        )
                                        .into(),
                                        Expr::String("user-info".into()).into()
                                    )
                                    .into()
                                )
                                .into(),
                                Expr::Bool(true).into()
                            )
                            .into(),
                            Expr::String("settings".into()).into()
                        )
                        .into()
                    )
                    .into(),
                    Expr::Null.into()
                )
                .into()
            )
        );
    }

    #[test]
    fn test_unary_not_operator() {
        let result = parse("not true").unwrap();
        assert_eq!(result, Expr::Not(Expr::Bool(true).into()));

        let result = parse("not false").unwrap();
        assert_eq!(result, Expr::Not(Expr::Bool(false).into()));

        let result = parse("not null").unwrap();
        assert_eq!(result, Expr::Not(Expr::Null.into()));

        let result = parse("not .active").unwrap();
        assert_eq!(
            result,
            Expr::Not(
                Expr::Index(Expr::Identity.into(), Expr::String("active".into()).into()).into()
            )
        );

        let result = parse("not not true").unwrap();
        assert_eq!(result, Expr::Not(Expr::Not(Expr::Bool(true).into()).into()));

        let result = parse("not (.age > 18)").unwrap();
        assert_eq!(
            result,
            Expr::Not(
                Expr::Greater(
                    Expr::Index(Expr::Identity.into(), Expr::String("age".into()).into()).into(),
                    Expr::Number(Int(18).into()).into()
                )
                .into()
            )
        );

        let result = parse("not .active and .verified").unwrap();
        assert_eq!(
            result,
            Expr::And(
                Expr::Not(
                    Expr::Index(Expr::Identity.into(), Expr::String("active".into()).into()).into()
                )
                .into(),
                Expr::Index(
                    Expr::Identity.into(),
                    Expr::String("verified".into()).into()
                )
                .into()
            )
        );

        let result = parse("not true and false").unwrap();
        assert_eq!(
            result,
            Expr::And(
                Expr::Not(Expr::Bool(true).into()).into(),
                Expr::Bool(false).into()
            )
        );

        let result = parse("not true or false").unwrap();
        assert_eq!(
            result,
            Expr::Or(
                Expr::Not(Expr::Bool(true).into()).into(),
                Expr::Bool(false).into()
            )
        );
    }

    #[test]
    fn test_object_construction_shorthands() {
        let result = parse("{name}").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![(
                Expr::String("name".into()),
                Expr::Index(Expr::Identity.into(), Expr::String("name".into()).into())
            )])
        );

        let result = parse("{name, age, active}").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("name".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("name".into()).into())
                ),
                (
                    Expr::String("age".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("age".into()).into())
                ),
                (
                    Expr::String("active".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("active".into()).into())
                )
            ])
        );

        let result = parse("{name, age: .user.age, active}").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("name".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("name".into()).into())
                ),
                (
                    Expr::String("age".into()),
                    Expr::Index(
                        Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into())
                            .into(),
                        Expr::String("age".into()).into()
                    )
                ),
                (
                    Expr::String("active".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("active".into()).into())
                )
            ])
        );

        let result = parse(r#"{"user-name"}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![(
                Expr::String("user-name".into()),
                Expr::Index(
                    Expr::Identity.into(),
                    Expr::String("user-name".into()).into()
                )
            )])
        );

        let result = parse("{true, false, null}").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::Bool(true),
                    Expr::Index(Expr::Identity.into(), Expr::Bool(true).into())
                ),
                (
                    Expr::Bool(false),
                    Expr::Index(Expr::Identity.into(), Expr::Bool(false).into())
                ),
                (
                    Expr::Null,
                    Expr::Index(Expr::Identity.into(), Expr::Null.into())
                )
            ])
        );

        let result =
            parse(r#"{name, "full-name": .user.name, active, count: length(.items), verified}"#)
                .unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("name".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("name".into()).into())
                ),
                (
                    Expr::String("full-name".into()),
                    Expr::Index(
                        Expr::Index(Expr::Identity.into(), Expr::String("user".into()).into())
                            .into(),
                        Expr::String("name".into()).into()
                    )
                ),
                (
                    Expr::String("active".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("active".into()).into())
                ),
                (
                    Expr::String("count".into()),
                    Expr::Call(
                        "length",
                        vec![Expr::Index(
                            Expr::Identity.into(),
                            Expr::String("items".into()).into()
                        )]
                    )
                ),
                (
                    Expr::String("verified".into()),
                    Expr::Index(
                        Expr::Identity.into(),
                        Expr::String("verified".into()).into()
                    )
                )
            ])
        );

        let result = parse("{user: {name, age}, settings: {theme}}").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("user".into()),
                    Expr::Object(vec![
                        (
                            Expr::String("name".into()),
                            Expr::Index(Expr::Identity.into(), Expr::String("name".into()).into())
                        ),
                        (
                            Expr::String("age".into()),
                            Expr::Index(Expr::Identity.into(), Expr::String("age".into()).into())
                        )
                    ])
                ),
                (
                    Expr::String("settings".into()),
                    Expr::Object(vec![(
                        Expr::String("theme".into()),
                        Expr::Index(Expr::Identity.into(), Expr::String("theme".into()).into())
                    )])
                )
            ])
        );
    }

    #[test]
    fn test_not_and_negate_precedence() {
        let result = parse("not -5").unwrap();
        assert_eq!(
            result,
            Expr::Not(Expr::Negate(Expr::Number(Int(5).into()).into()).into())
        );

        let result = parse("-not true").unwrap();
        assert_eq!(
            result,
            Expr::Negate(Expr::Not(Expr::Bool(true).into()).into())
        );

        let result = parse("-(not true)").unwrap();
        assert_eq!(
            result,
            Expr::Negate(Expr::Not(Expr::Bool(true).into()).into())
        );

        let result = parse("not (-5)").unwrap();
        assert_eq!(
            result,
            Expr::Not(Expr::Negate(Expr::Number(Int(5).into()).into()).into())
        );
    }

    #[test]
    fn test_object_shorthand_edge_cases() {
        let result = parse("{(.dynamic)}");
        assert!(
            result.is_err(),
            "Expected {{(.dynamic)}} to fail - computed keys need colon"
        );

        let result = parse("{(.dynamic): .value}").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![(
                Expr::Index(Expr::Identity.into(), Expr::String("dynamic".into()).into()),
                Expr::Index(Expr::Identity.into(), Expr::String("value".into()).into())
            )])
        );

        let result = parse("{}").unwrap();
        assert_eq!(result, Expr::Object(vec![]));

        let result = parse("{name, age}").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("name".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("name".into()).into())
                ),
                (
                    Expr::String("age".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("age".into()).into())
                )
            ])
        );
    }

    #[test]
    fn test_jq_compatibility_examples() {
        let test_cases = vec![
            ("not true", "not true"), // basic not operation
            ("not false", "not false"),
            ("not null", "not null"),
            ("not 0", "not 0"),               // not with number
            ("not \"\"", "not \"\""),         // not with empty string
            ("not []", "not []"),             // not with empty array
            ("not {}", "not {}"),             // not with empty object
            ("not .foo", "not .foo"),         // not with field access
            ("not (.x > 5)", "not (.x > 5)"), // not with comparison
        ];

        for (input, _description) in test_cases {
            let result = parse(input);
            assert!(
                result.is_ok(),
                "Failed to parse jq-compatible expression: {}",
                input
            );
        }

        let shorthand_cases = vec![
            ("{foo}", "basic shorthand"),
            ("{foo, bar}", "multiple shorthands"),
            ("{foo, bar: .baz}", "mixed shorthand and regular"),
            ("{\"foo-bar\"}", "quoted shorthand"),
            ("{true, false, null}", "literal shorthands"),
            ("{x, y: .y, z}", "complex mixed"),
        ];

        for (input, _description) in shorthand_cases {
            let result = parse(input);
            assert!(
                result.is_ok(),
                "Failed to parse jq-compatible shorthand: {}",
                input
            );
        }
    }

    #[test]
    fn test_operator_precedence_with_new_features() {
        let result = parse("true and not false").unwrap();
        assert_eq!(
            result,
            Expr::And(
                Expr::Bool(true).into(),
                Expr::Not(Expr::Bool(false).into()).into()
            )
        );

        let result = parse("not true or false").unwrap();
        assert_eq!(
            result,
            Expr::Or(
                Expr::Not(Expr::Bool(true).into()).into(),
                Expr::Bool(false).into()
            )
        );

        let result = parse("not -5 + 3").unwrap();
        assert_eq!(
            result,
            Expr::Add(
                Expr::Not(Expr::Negate(Expr::Number(Int(5).into()).into()).into()).into(),
                Expr::Number(Int(3).into()).into()
            )
        );

        let result = parse(".active | not .disabled").unwrap();
        assert_eq!(
            result,
            Expr::Pipe(
                Expr::Index(Expr::Identity.into(), Expr::String("active".into()).into()).into(),
                Expr::Not(
                    Expr::Index(
                        Expr::Identity.into(),
                        Expr::String("disabled".into()).into()
                    )
                    .into()
                )
                .into()
            )
        );
    }

    #[test]
    fn test_complex_expressions_with_new_features() {
        let result = parse("{active: not .disabled, name, verified: not not .checked}").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("active".into()),
                    Expr::Not(
                        Expr::Index(
                            Expr::Identity.into(),
                            Expr::String("disabled".into()).into()
                        )
                        .into()
                    )
                ),
                (
                    Expr::String("name".into()),
                    Expr::Index(Expr::Identity.into(), Expr::String("name".into()).into())
                ),
                (
                    Expr::String("verified".into()),
                    Expr::Not(
                        Expr::Not(
                            Expr::Index(
                                Expr::Identity.into(),
                                Expr::String("checked".into()).into()
                            )
                            .into()
                        )
                        .into()
                    )
                )
            ])
        );

        let result = parse(".users | map({name, active: not .disabled})").unwrap();
        assert_eq!(
            result,
            Expr::Pipe(
                Expr::Index(Expr::Identity.into(), Expr::String("users".into()).into()).into(),
                Expr::Call(
                    "map",
                    vec![Expr::Object(vec![
                        (
                            Expr::String("name".into()),
                            Expr::Index(Expr::Identity.into(), Expr::String("name".into()).into())
                        ),
                        (
                            Expr::String("active".into()),
                            Expr::Not(
                                Expr::Index(
                                    Expr::Identity.into(),
                                    Expr::String("disabled".into()).into()
                                )
                                .into()
                            )
                        )
                    ])]
                )
                .into()
            )
        );
    }

    #[test]
    fn test_double_negation() {
        let result = parse("- -5").unwrap();
        assert_eq!(
            result,
            Expr::Negate(Expr::Negate(Expr::Number(Int(5).into()).into()).into())
        );

        let result = parse("- - -42").unwrap();
        assert_eq!(
            result,
            Expr::Negate(
                Expr::Negate(Expr::Negate(Expr::Number(Int(42).into()).into()).into()).into()
            )
        );

        let result = parse("1 + - -3").unwrap();
        assert_eq!(
            result,
            Expr::Add(
                Expr::Number(Int(1).into()).into(),
                Expr::Negate(Expr::Negate(Expr::Number(Int(3).into()).into()).into()).into()
            )
        );

        let result = parse("-(- 7)").unwrap();
        assert_eq!(
            result,
            Expr::Negate(Expr::Negate(Expr::Number(Int(7).into()).into()).into())
        );
    }

    #[test]
    fn test_simple_variable_destructuring() {
        let result = parse(". as $var | $var").unwrap();
        assert_eq!(
            result,
            Expr::Block(
                Pattern::Variable("var"),
                Expr::Identity.into(),
                Expr::Binding("var").into()
            )
        );
    }

    #[test]
    fn test_array_destructuring() {
        let result = parse(". as [$first, $second] | $first + $second").unwrap();
        assert_eq!(
            result,
            Expr::Block(
                Pattern::Array(vec![
                    Pattern::Variable("first"),
                    Pattern::Variable("second")
                ]),
                Expr::Identity.into(),
                Expr::Add(
                    Expr::Binding("first").into(),
                    Expr::Binding("second").into()
                )
                .into()
            )
        );
    }

    #[test]
    fn test_object_destructuring_simple() {
        let result = parse(". as {name: $n, age: $a} | $n").unwrap();
        assert_eq!(
            result,
            Expr::Block(
                Pattern::Object(vec![
                    (Expr::String("name".into()), Pattern::Variable("n")),
                    (Expr::String("age".into()), Pattern::Variable("a"))
                ]),
                Expr::Identity.into(),
                Expr::Binding("n").into()
            )
        );
    }

    #[test]
    fn test_object_destructuring_shorthand_rejected() {
        // jq doesn't support shorthand syntax like {name, age} - it requires explicit bindings
        let result = parse(". as {name, age} | name");
        assert!(
            result.is_err(),
            "Shorthand syntax should be rejected to match jq behavior"
        );
    }

    #[test]
    fn test_object_destructuring_with_binding_shorthand() {
        let result = parse(". as {$name, age: $a} | $name").unwrap();
        assert_eq!(
            result,
            Expr::Block(
                Pattern::Object(vec![
                    (Expr::String("name".into()), Pattern::Variable("name")),
                    (Expr::String("age".into()), Pattern::Variable("a"))
                ]),
                Expr::Identity.into(),
                Expr::Binding("name").into()
            )
        );
    }

    #[test]
    fn test_nested_array_destructuring() {
        let result = parse(". as [[$x, $y], $z] | $x + $y + $z").unwrap();
        assert_eq!(
            result,
            Expr::Block(
                Pattern::Array(vec![
                    Pattern::Array(vec![Pattern::Variable("x"), Pattern::Variable("y")]),
                    Pattern::Variable("z")
                ]),
                Expr::Identity.into(),
                Expr::Add(
                    Expr::Add(Expr::Binding("x").into(), Expr::Binding("y").into()).into(),
                    Expr::Binding("z").into()
                )
                .into()
            )
        );
    }

    #[test]
    fn test_nested_object_destructuring() {
        let result = parse(". as {user: {name: $n, age: $a}} | $n").unwrap();
        assert_eq!(
            result,
            Expr::Block(
                Pattern::Object(vec![(
                    Expr::String("user".into()),
                    Pattern::Object(vec![
                        (Expr::String("name".into()), Pattern::Variable("n")),
                        (Expr::String("age".into()), Pattern::Variable("a"))
                    ])
                )]),
                Expr::Identity.into(),
                Expr::Binding("n").into()
            )
        );
    }

    #[test]
    fn test_mixed_nested_destructuring() {
        let result = parse(". as {realnames: [$first, $second], posts: $p} | $first").unwrap();
        assert_eq!(
            result,
            Expr::Block(
                Pattern::Object(vec![
                    (
                        Expr::String("realnames".into()),
                        Pattern::Array(vec![
                            Pattern::Variable("first"),
                            Pattern::Variable("second")
                        ])
                    ),
                    (Expr::String("posts".into()), Pattern::Variable("p"))
                ]),
                Expr::Identity.into(),
                Expr::Binding("first").into()
            )
        );
    }

    #[test]
    fn test_object_destructuring_with_computed_key() {
        let result = parse(r#". as {("key"): $val} | $val"#).unwrap();
        assert_eq!(
            result,
            Expr::Block(
                Pattern::Object(vec![(Expr::String("key".into()), Pattern::Variable("val"))]),
                Expr::Identity.into(),
                Expr::Binding("val").into()
            )
        );
    }

    #[test]
    fn test_empty_destructuring_patterns_rejected() {
        // jq doesn't support empty patterns
        let result = parse(". as [] | .");
        assert!(
            result.is_err(),
            "Empty array patterns should be rejected to match jq behavior"
        );

        let result = parse(". as {} | .");
        assert!(
            result.is_err(),
            "Empty object patterns should be rejected to match jq behavior"
        );
    }

    #[test]
    fn test_complex_destructuring_example() {
        let result = parse(
            r#".users | map(. as {name: $n, profile: {age: $a, settings: [$theme, $lang]}} | {name: $n, age: $a, theme: $theme})"#
        ).unwrap();

        // This is a complex expression, let's just verify it parses without error
        // and has the expected top-level structure
        match result {
            Expr::Pipe(left, right) => {
                assert_eq!(
                    *left,
                    Expr::Index(Expr::Identity.into(), Expr::String("users".into()).into())
                );
                match *right {
                    Expr::Call(name, args) => {
                        assert_eq!(name, "map");
                        assert_eq!(args.len(), 1);
                        // The argument should be a Block expression with nested patterns
                        match &args[0] {
                            Expr::Block(pattern, _, _) => {
                                match pattern {
                                    Pattern::Object(pairs) => {
                                        assert_eq!(pairs.len(), 2);
                                        // Verify the structure exists
                                        assert_eq!(pairs[0].0, Expr::String("name".into()));
                                        assert_eq!(pairs[1].0, Expr::String("profile".into()));
                                    }
                                    _ => panic!("Expected object pattern"),
                                }
                            }
                            _ => panic!("Expected Block expression"),
                        }
                    }
                    _ => panic!("Expected Call expression"),
                }
            }
            _ => panic!("Expected Pipe expression"),
        }
    }

    #[test]
    fn test_simple_destructuring_alternative() {
        let result = parse(". as $var ?// {value: $var} | $var").unwrap();
        assert_eq!(
            result,
            Expr::Block(
                Pattern::Alternative(
                    Pattern::Variable("var").into(),
                    Pattern::Object(vec![(
                        Expr::String("value".into()),
                        Pattern::Variable("var")
                    )])
                    .into()
                ),
                Expr::Identity.into(),
                Expr::Binding("var").into()
            )
        );
    }

    #[test]
    fn test_multiple_destructuring_alternatives() {
        let result = parse(". as $x ?// [$x] ?// {value: $x} | $x").unwrap();
        assert_eq!(
            result,
            Expr::Block(
                Pattern::Alternative(
                    Pattern::Alternative(
                        Pattern::Variable("x").into(),
                        Pattern::Array(vec![Pattern::Variable("x")]).into()
                    )
                    .into(),
                    Pattern::Object(vec![(Expr::String("value".into()), Pattern::Variable("x"))])
                        .into()
                ),
                Expr::Identity.into(),
                Expr::Binding("x").into()
            )
        );
    }

    #[test]
    fn test_array_destructuring_alternatives() {
        let result = parse(". as [$x, $y] ?// [$x] | $x").unwrap();
        assert_eq!(
            result,
            Expr::Block(
                Pattern::Alternative(
                    Pattern::Array(vec![Pattern::Variable("x"), Pattern::Variable("y")]).into(),
                    Pattern::Array(vec![Pattern::Variable("x")]).into()
                ),
                Expr::Identity.into(),
                Expr::Binding("x").into()
            )
        );
    }

    #[test]
    fn test_object_destructuring_alternatives() {
        let result = parse(". as {name: $n, age: $a} ?// {name: $n} | $n").unwrap();
        assert_eq!(
            result,
            Expr::Block(
                Pattern::Alternative(
                    Pattern::Object(vec![
                        (Expr::String("name".into()), Pattern::Variable("n")),
                        (Expr::String("age".into()), Pattern::Variable("a"))
                    ])
                    .into(),
                    Pattern::Object(vec![(Expr::String("name".into()), Pattern::Variable("n"))])
                        .into()
                ),
                Expr::Identity.into(),
                Expr::Binding("n").into()
            )
        );
    }

    #[test]
    fn test_nested_alternatives_with_mixed_patterns() {
        let result = parse(". as {users: [$u1, $u2]} ?// {user: $u1} ?// $u1 | $u1").unwrap();

        // Verify the top-level structure
        match result {
            Expr::Block(pattern, value_expr, body_expr) => {
                assert_eq!(*value_expr, Expr::Identity);
                assert_eq!(*body_expr, Expr::Binding("u1"));

                // Verify the pattern structure
                match pattern {
                    Pattern::Alternative(left, right) => {
                        match (left.as_ref(), right.as_ref()) {
                            (
                                Pattern::Alternative(inner_left, inner_right),
                                Pattern::Variable("u1"),
                            ) => {
                                // First alternative: {users: [$u1, $u2]}
                                match inner_left.as_ref() {
                                    Pattern::Object(pairs) => {
                                        assert_eq!(pairs.len(), 1);
                                        assert_eq!(pairs[0].0, Expr::String("users".into()));
                                        match &pairs[0].1 {
                                            Pattern::Array(vars) => {
                                                assert_eq!(vars.len(), 2);
                                                assert_eq!(vars[0], Pattern::Variable("u1"));
                                                assert_eq!(vars[1], Pattern::Variable("u2"));
                                            }
                                            _ => panic!("Expected array pattern"),
                                        }
                                    }
                                    _ => panic!("Expected object pattern"),
                                }

                                // Second alternative: {user: $u1}
                                match inner_right.as_ref() {
                                    Pattern::Object(pairs) => {
                                        assert_eq!(pairs.len(), 1);
                                        assert_eq!(pairs[0].0, Expr::String("user".into()));
                                        assert_eq!(pairs[0].1, Pattern::Variable("u1"));
                                    }
                                    _ => panic!("Expected object pattern"),
                                }
                            }
                            _ => panic!("Expected nested alternative structure"),
                        }
                    }
                    _ => panic!("Expected alternative pattern"),
                }
            }
            _ => panic!("Expected Block expression"),
        }
    }

    #[test]
    fn test_destructuring_example_from_manual() {
        let _result = parse(".resources as {$id, $kind, events: {$user_id, $ts}} ?// {$id, $kind, events: [{$user_id, $ts}]} | {$user_id, $kind, $id, $ts}").unwrap();
    }

    #[test]
    fn test_string_interpolation() {
        let result = parse(r#""Hello, \(.name)!""#).unwrap();
        assert!(matches!(result, Expr::InterpolatedString(_)));

        let result = parse(r#""Count: \(length(.items))""#).unwrap();
        assert!(matches!(result, Expr::InterpolatedString(_)));

        let result = parse(r#""Sum: \(.a + .b)""#).unwrap();
        assert!(matches!(result, Expr::InterpolatedString(_)));
    }

    #[test]
    fn test_string_interpolation_comprehensive() {
        use std::borrow::Cow;

        // Test basic interpolation with field access
        let result = parse(r#""Hello, \(.name)!""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 3);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Text(Cow::Borrowed("Hello, "))
            );
            assert_eq!(
                parts[1],
                InterpolatedStringPart::Expr(Expr::Index(
                    Expr::Identity.into(),
                    Expr::String(Cow::Borrowed("name")).into()
                ))
            );
            assert_eq!(parts[2], InterpolatedStringPart::Text(Cow::Borrowed("!")));
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test from jq test suite: "inter\("pol" + "ation")" -> "interpolation"
        let result = parse(r#""inter\("pol" + "ation")""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 2);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Text(Cow::Borrowed("inter"))
            );
            assert_eq!(
                parts[1],
                InterpolatedStringPart::Expr(Expr::Add(
                    Expr::String(Cow::Borrowed("pol")).into(),
                    Expr::String(Cow::Borrowed("ation")).into()
                ))
            );
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test arithmetic expressions in interpolation
        let result = parse(r#""Sum: \(.a + .b), Product: \(.a * .b)""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 4);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Text(Cow::Borrowed("Sum: "))
            );
            assert_eq!(
                parts[1],
                InterpolatedStringPart::Expr(Expr::Add(
                    Expr::Index(
                        Expr::Identity.into(),
                        Expr::String(Cow::Borrowed("a")).into()
                    )
                    .into(),
                    Expr::Index(
                        Expr::Identity.into(),
                        Expr::String(Cow::Borrowed("b")).into()
                    )
                    .into()
                ))
            );
            assert_eq!(
                parts[2],
                InterpolatedStringPart::Text(Cow::Borrowed(", Product: "))
            );
            assert_eq!(
                parts[3],
                InterpolatedStringPart::Expr(Expr::Multiply(
                    Expr::Index(
                        Expr::Identity.into(),
                        Expr::String(Cow::Borrowed("a")).into()
                    )
                    .into(),
                    Expr::Index(
                        Expr::Identity.into(),
                        Expr::String(Cow::Borrowed("b")).into()
                    )
                    .into()
                ))
            );
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test function calls in interpolation
        let result = parse(r#""Length: \(length(.items))""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 2);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Text(Cow::Borrowed("Length: "))
            );
            assert_eq!(
                parts[1],
                InterpolatedStringPart::Expr(Expr::Call(
                    "length",
                    vec![Expr::Index(
                        Expr::Identity.into(),
                        Expr::String(Cow::Borrowed("items")).into()
                    )]
                ))
            );
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test pipe expressions in interpolation
        let result = parse(r#""Upper: \(. | length)""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 2);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Text(Cow::Borrowed("Upper: "))
            );
            assert_eq!(
                parts[1],
                InterpolatedStringPart::Expr(Expr::Pipe(
                    Expr::Identity.into(),
                    Expr::Call("length", vec![]).into()
                ))
            );
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test identity interpolation
        let result = parse(r#""Value: \(.)""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 2);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Text(Cow::Borrowed("Value: "))
            );
            assert_eq!(parts[1], InterpolatedStringPart::Expr(Expr::Identity));
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test boolean and number literals in interpolation
        let result = parse(r#""Bool: \(true), Number: \(42)""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 4);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Text(Cow::Borrowed("Bool: "))
            );
            assert_eq!(parts[1], InterpolatedStringPart::Expr(Expr::Bool(true)));
            assert_eq!(
                parts[2],
                InterpolatedStringPart::Text(Cow::Borrowed(", Number: "))
            );
            assert_eq!(
                parts[3],
                InterpolatedStringPart::Expr(Expr::Number(Int(42).into()))
            );
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test null literal in interpolation
        let result = parse(r#""Null: \(null)""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 2);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Text(Cow::Borrowed("Null: "))
            );
            assert_eq!(parts[1], InterpolatedStringPart::Expr(Expr::Null));
        } else {
            panic!("Expected InterpolatedString");
        }
    }

    #[test]
    fn test_string_interpolation_edge_cases() {
        use std::borrow::Cow;

        // Test empty string interpolation
        let result = parse(r#""\(.)""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 1);
            assert_eq!(parts[0], InterpolatedStringPart::Expr(Expr::Identity));
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test string starting with interpolation
        let result = parse(r#""\(.name) says hello""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 2);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Expr(Expr::Index(
                    Expr::Identity.into(),
                    Expr::String(Cow::Borrowed("name")).into()
                ))
            );
            assert_eq!(
                parts[1],
                InterpolatedStringPart::Text(Cow::Borrowed(" says hello"))
            );
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test string ending with interpolation
        let result = parse(r#""Hello \(.name)""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 2);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Text(Cow::Borrowed("Hello "))
            );
            assert_eq!(
                parts[1],
                InterpolatedStringPart::Expr(Expr::Index(
                    Expr::Identity.into(),
                    Expr::String(Cow::Borrowed("name")).into()
                ))
            );
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test multiple consecutive interpolations
        let result = parse(r#""\(.a)\(.b)\(.c)""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 3);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Expr(Expr::Index(
                    Expr::Identity.into(),
                    Expr::String(Cow::Borrowed("a")).into()
                ))
            );
            assert_eq!(
                parts[1],
                InterpolatedStringPart::Expr(Expr::Index(
                    Expr::Identity.into(),
                    Expr::String(Cow::Borrowed("b")).into()
                ))
            );
            assert_eq!(
                parts[2],
                InterpolatedStringPart::Expr(Expr::Index(
                    Expr::Identity.into(),
                    Expr::String(Cow::Borrowed("c")).into()
                ))
            );
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test complex nested expressions
        let result = parse(r#""Result: \(.data[0].user?.name // "unknown")""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 2);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Text(Cow::Borrowed("Result: "))
            );
            // The second part should be a complex expression with Alt, Opt, Index, etc.
            match &parts[1] {
                InterpolatedStringPart::Expr(expr) => {
                    // Verify it's an Alt expression (// operator)
                    assert!(matches!(expr, Expr::Alt(_, _)));
                }
                _ => panic!("Expected interpolated expression"),
            }
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test array and object literals in interpolation
        let result = parse(r#""Array: \([1,2,3]), Object: \({key: "value"})""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 4);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Text(Cow::Borrowed("Array: "))
            );
            assert_eq!(
                parts[1],
                InterpolatedStringPart::Expr(Expr::Array(vec![
                    Expr::Number(Int(1).into()),
                    Expr::Number(Int(2).into()),
                    Expr::Number(Int(3).into())
                ]))
            );
            assert_eq!(
                parts[2],
                InterpolatedStringPart::Text(Cow::Borrowed(", Object: "))
            );
            assert_eq!(
                parts[3],
                InterpolatedStringPart::Expr(Expr::Object(vec![(
                    Expr::String(Cow::Borrowed("key")),
                    Expr::String(Cow::Borrowed("value"))
                )]))
            );
        } else {
            panic!("Expected InterpolatedString");
        }

        // Test escape sequences with interpolation
        let result = parse(r#""Line1\nResult: \(.value)\tEnd""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            // The lexer separates escape sequences into individual parts
            assert_eq!(parts.len(), 6);
            assert_eq!(
                parts[0],
                InterpolatedStringPart::Text(Cow::Borrowed("Line1"))
            );
            assert_eq!(parts[1], InterpolatedStringPart::Text(Cow::Borrowed("\n")));
            assert_eq!(
                parts[2],
                InterpolatedStringPart::Text(Cow::Borrowed("Result: "))
            );
            assert_eq!(
                parts[3],
                InterpolatedStringPart::Expr(Expr::Index(
                    Expr::Identity.into(),
                    Expr::String(Cow::Borrowed("value")).into()
                ))
            );
            assert_eq!(parts[4], InterpolatedStringPart::Text(Cow::Borrowed("\t")));
            assert_eq!(parts[5], InterpolatedStringPart::Text(Cow::Borrowed("End")));
        } else {
            panic!("Expected InterpolatedString");
        }
    }

    #[test]
    fn test_string_interpolation_jq_compatibility_examples() {
        use std::borrow::Cow;

        // Examples from jq test suite and manual

        // Basic example from jq manual
        let result = parse(r#""The input was \(.), which is one less than \(.+1)""#).unwrap();
        assert!(matches!(result, Expr::InterpolatedString(_)));

        // From jq.test: @html "<b>\(.)</b>"
        let result = parse(r#""<b>\(.)</b>""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 3);
            assert_eq!(parts[0], InterpolatedStringPart::Text(Cow::Borrowed("<b>")));
            assert_eq!(parts[1], InterpolatedStringPart::Expr(Expr::Identity));
            assert_eq!(
                parts[2],
                InterpolatedStringPart::Text(Cow::Borrowed("</b>"))
            );
        } else {
            panic!("Expected InterpolatedString");
        }

        // From jq.test: "a$\(1+1)"
        let result = parse(r#""a$\(1+1)""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 2);
            assert_eq!(parts[0], InterpolatedStringPart::Text(Cow::Borrowed("a$")));
            assert_eq!(
                parts[1],
                InterpolatedStringPart::Expr(Expr::Add(
                    Expr::Number(Int(1).into()).into(),
                    Expr::Number(Int(1).into()).into()
                ))
            );
        } else {
            panic!("Expected InterpolatedString");
        }

        // From jq.test: "\(.) there!"
        let result = parse(r#""\(.) there!""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 2);
            assert_eq!(parts[0], InterpolatedStringPart::Expr(Expr::Identity));
            assert_eq!(
                parts[1],
                InterpolatedStringPart::Text(Cow::Borrowed(" there!"))
            );
        } else {
            panic!("Expected InterpolatedString");
        }

        // From jq.test: "foo\(.)"
        let result = parse(r#""foo\(.)""#).unwrap();
        if let Expr::InterpolatedString(parts) = result {
            assert_eq!(parts.len(), 2);
            assert_eq!(parts[0], InterpolatedStringPart::Text(Cow::Borrowed("foo")));
            assert_eq!(parts[1], InterpolatedStringPart::Expr(Expr::Identity));
        } else {
            panic!("Expected InterpolatedString");
        }
    }
}
