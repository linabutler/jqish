// Copyright (c) 2025 Lina Butler
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::{borrow::Cow, str::FromStr};

use lalrpop_util::{ParseError as LalrpopParseError, lalrpop_mod};

use crate::error::LexicalError;

use super::{error::SpannedError, lexer::Lexer};

lalrpop_mod!(jqish);

/// Parses a string containing a `jq`-like filter expression
/// into an expression tree.
pub fn parse(input: &str) -> Result<Expr<'_>, SpannedError<LexicalError>> {
    let lexer = Lexer::new(input);
    let parser = jqish::ExprParser::new();
    parser.parse(input, lexer).map_err(|err| match err {
        LalrpopParseError::ExtraToken {
            token: (start, _, end),
        } => SpannedError {
            error: LexicalError::BadToken,
            location: (start, end),
        },
        LalrpopParseError::InvalidToken { location: start } => SpannedError {
            error: LexicalError::BadToken,
            location: (start, input.len()),
        },
        LalrpopParseError::UnrecognizedEOF {
            location: start, ..
        } => SpannedError {
            error: LexicalError::BadToken,
            location: (start, input.len()),
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

    /// The recursive descent operator, `..`. This operator yields
    /// every descendant of `.` to the next filter.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// let expr = parse("..").unwrap();
    /// assert_eq!(expr, Expr::RecursiveDescent);
    /// ```
    RecursiveDescent,

    /// An integer or floating-point literal.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("42").unwrap();
    /// assert_eq!(expr, Expr::Number(Number::Int(42)));
    ///
    /// let expr = parse("3.14").unwrap();
    /// assert_eq!(expr, Expr::Number(Number::Float(3.14)));
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
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("[]").unwrap();
    /// assert_eq!(expr, Expr::Array(vec![]));
    ///
    /// let expr = parse("[1, 2, 3]").unwrap();
    /// assert_eq!(expr, Expr::Array(vec![
    ///     Expr::Number(Number::Int(1)),
    ///     Expr::Number(Number::Int(2)),
    ///     Expr::Number(Number::Int(3)),
    /// ]));
    /// ```
    Array(Vec<Expr<'a>>),

    /// An object literal.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use std::borrow::Cow;
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("{}").unwrap();
    /// assert_eq!(expr, Expr::Object(vec![]));
    ///
    /// let expr = parse("{name, age: 30}").unwrap();
    /// assert_eq!(expr, Expr::Object(vec![
    ///     (Expr::String(Cow::Borrowed("name")), Expr::String(Cow::Borrowed("name"))),
    ///     (Expr::String(Cow::Borrowed("age")), Expr::Number(Number::Int(30))),
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
    ///     Box::new(Expr::Index(
    ///         Box::new(Expr::Identity),
    ///         Box::new(Expr::String(Cow::Borrowed("user")))
    ///     )),
    ///     Box::new(Expr::Index(
    ///         Box::new(Expr::Identity),
    ///         Box::new(Expr::String(Cow::Borrowed("name")))
    ///     ))
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
    ///     Box::new(Expr::Bool(true)),
    ///     Box::new(Expr::Bool(false))
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
    ///     Box::new(Expr::Bool(true)),
    ///     Box::new(Expr::Bool(false))
    /// ));
    ///
    /// // `and` binds tighter than `or`.
    /// let expr = parse("true and false or null").unwrap();
    /// assert_eq!(expr, Expr::Or(
    ///     Box::new(Expr::And(
    ///         Box::new(Expr::Bool(true)),
    ///         Box::new(Expr::Bool(false))
    ///     )),
    ///     Box::new(Expr::Null)
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
    /// assert_eq!(expr, Expr::Alternative(
    ///     Box::new(Expr::Index(
    ///         Box::new(Expr::Identity),
    ///         Box::new(Expr::String(Cow::Borrowed("name")))
    ///     )),
    ///     Box::new(Expr::String(Cow::Borrowed("Unknown")))
    /// ));
    /// ```
    Alternative(Box<Expr<'a>>, Box<Expr<'a>>),

    /// An equality expression, `a == b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("1 == 2").unwrap();
    /// assert_eq!(expr, Expr::Equal(
    ///     Box::new(Expr::Number(Number::Int(1))),
    ///     Box::new(Expr::Number(Number::Int(2)))
    /// ));
    /// ```
    Equal(Box<Expr<'a>>, Box<Expr<'a>>),

    /// An inequality expression, `a != b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("1 != 2").unwrap();
    /// assert_eq!(expr, Expr::NotEqual(
    ///     Box::new(Expr::Number(Number::Int(1))),
    ///     Box::new(Expr::Number(Number::Int(2)))
    /// ));
    /// ```
    NotEqual(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A less-than expression, `a < b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("1 < 2").unwrap();
    /// assert_eq!(expr, Expr::Less(
    ///     Box::new(Expr::Number(Number::Int(1))),
    ///     Box::new(Expr::Number(Number::Int(2)))
    /// ));
    /// ```
    Less(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A greater-than expression, `a > b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("1 > 2").unwrap();
    /// assert_eq!(expr, Expr::Greater(
    ///     Box::new(Expr::Number(Number::Int(1))),
    ///     Box::new(Expr::Number(Number::Int(2)))
    /// ));
    /// ```
    Greater(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A less-than-or-equal expression, `a <= b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("1 <= 2").unwrap();
    /// assert_eq!(expr, Expr::LessEqual(
    ///     Box::new(Expr::Number(Number::Int(1))),
    ///     Box::new(Expr::Number(Number::Int(2)))
    /// ));
    /// ```
    LessEqual(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A greater-than-or-equal expression, `a >= b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("1 >= 2").unwrap();
    /// assert_eq!(expr, Expr::GreaterEqual(
    ///     Box::new(Expr::Number(Number::Int(1))),
    ///     Box::new(Expr::Number(Number::Int(2)))
    /// ));
    /// ```
    GreaterEqual(Box<Expr<'a>>, Box<Expr<'a>>),

    /// An addition expression, `a + b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("1 + 2").unwrap();
    /// assert_eq!(expr, Expr::Add(
    ///     Box::new(Expr::Number(Number::Int(1))),
    ///     Box::new(Expr::Number(Number::Int(2)))
    /// ));
    /// ```
    Add(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A subtraction expression, `a - b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("1 - 2").unwrap();
    /// assert_eq!(expr, Expr::Subtract(
    ///     Box::new(Expr::Number(Number::Int(1))),
    ///     Box::new(Expr::Number(Number::Int(2)))
    /// ));
    /// ```
    Subtract(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A multiplication expression, `a * b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("1 * 2").unwrap();
    /// assert_eq!(expr, Expr::Multiply(
    ///     Box::new(Expr::Number(Number::Int(1))),
    ///     Box::new(Expr::Number(Number::Int(2)))
    /// ));
    /// ```
    Multiply(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A division expression, `a / b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("1 / 2").unwrap();
    /// assert_eq!(expr, Expr::Divide(
    ///     Box::new(Expr::Number(Number::Int(1))),
    ///     Box::new(Expr::Number(Number::Int(2)))
    /// ));
    /// ```
    Divide(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A modulo expression, `a % b`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("1 % 2").unwrap();
    /// assert_eq!(expr, Expr::Modulo(
    ///     Box::new(Expr::Number(Number::Int(1))),
    ///     Box::new(Expr::Number(Number::Int(2)))
    /// ));
    /// ```
    Modulo(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A negated expression, `-a`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse("-42").unwrap();
    /// assert_eq!(expr, Expr::Negate(Box::new(Expr::Number(Number::Int(42)))));
    /// ```
    Negate(Box<Expr<'a>>),

    /// A Boolean "not" expression, `not a`.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// let expr = parse("not true").unwrap();
    /// assert_eq!(expr, Expr::Not(Box::new(Expr::Bool(true))));
    ///
    /// // `not` binds tighter than `and` or `or`.
    /// let expr = parse("not true and false").unwrap();
    /// assert_eq!(expr, Expr::And(
    ///     Box::new(Expr::Not(Box::new(Expr::Bool(true)))),
    ///     Box::new(Expr::Bool(false))
    /// ));
    /// ```
    Not(Box<Expr<'a>>),

    /// An indexing operation, `.[expr]`, used to access
    /// array elements and object properties.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// # use std::borrow::Cow;
    /// let expr = parse(".[0]").unwrap();
    /// assert_eq!(expr, Expr::Index(
    ///     Box::new(Expr::Identity),
    ///     Box::new(Expr::Number(Number::Int(0)))
    /// ));
    ///
    /// let expr = parse(".name").unwrap();
    /// assert_eq!(expr, Expr::Index(
    ///     Box::new(Expr::Identity),
    ///     Box::new(Expr::String(Cow::Borrowed("name")))
    /// ));
    /// ```
    Index(Box<Expr<'a>>, Box<Expr<'a>>),

    /// An optional indexing operation, `.[expr]?`, which short-circuits to `null`
    /// if the element or property doesn't exist. This is sometimes called the
    /// "safe navigation operator" in other languages.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr};
    /// # use std::borrow::Cow;
    /// let expr = parse(".name?").unwrap();
    /// assert_eq!(expr, Expr::IndexOpt(
    ///     Box::new(Expr::Identity),
    ///     Box::new(Expr::String(Cow::Borrowed("name")))
    /// ));
    /// ```
    IndexOpt(Box<Expr<'a>>, Box<Expr<'a>>),

    /// A slice expression, `.[start:end]`. Both `start` and `end` are optional,
    /// and respectively default to the beginning and end of the array if omitted.
    ///
    /// ## Examples
    ///
    /// ```rust
    /// # use jqish::{parse, Expr, parser::Number};
    /// let expr = parse(".[1:3]").unwrap();
    /// assert_eq!(expr, Expr::Slice(
    ///     Box::new(Expr::Identity),
    ///     Some(Box::new(Expr::Number(Number::Int(1)))),
    ///     Some(Box::new(Expr::Number(Number::Int(3))))
    /// ));
    ///
    /// let expr = parse(".[2:]").unwrap();
    /// assert_eq!(expr, Expr::Slice(
    ///     Box::new(Expr::Identity),
    ///     Some(Box::new(Expr::Number(Number::Int(2)))),
    ///     None
    /// ));
    ///
    /// let expr = parse(".[:5]").unwrap();
    /// assert_eq!(expr, Expr::Slice(
    ///     Box::new(Expr::Identity),
    ///     None,
    ///     Some(Box::new(Expr::Number(Number::Int(5))))
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
    ///         Box::new(Expr::Identity),
    ///         Box::new(Expr::String(Cow::Borrowed("name"))),
    ///     ),
    /// ]));
    /// ```
    Call(&'a str, Vec<Expr<'a>>),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Number {
    Int(i64),
    Float(f64),
}

impl Number {
    pub fn from_int_str(s: &str) -> Result<Self, NumberError> {
        Ok(Self::Int(s.parse().map_err(|_| NumberError::NotInt)?))
    }
}

impl FromStr for Number {
    type Err = NumberError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_int_str(s)
            .or_else(|_| s.parse().map(Self::Float).map_err(|_| Self::Err::NotFloat))
    }
}

/// Removes surrounding quotes from, and expands escape sequences in,
/// a string literal.
pub fn unquote(s: &str) -> Result<Cow<'_, str>, SpannedError<BadEscapeError>> {
    if !s.contains('\\') {
        // If the string doesn't contain any escape sequences,
        // we can just drop the surrounding quotes and
        // return the contents.
        return Ok(Cow::Borrowed(&s[1..s.len() - 1]));
    }
    let mut string = String::with_capacity(s.len());
    let mut chars = s.char_indices().peekable();
    // Drop the surrounding quotes.
    let (_, quote) = chars.next().unwrap();
    let _ = chars.next_back().unwrap();
    while let Some((start, c)) = chars.next() {
        match c {
            '\\' => {
                let c = match chars.peek().unwrap() {
                    // Note: we don't support `\b`, `\f`, or `\uHHHH`
                    // escape sequences.
                    (_, 'n') => '\n',
                    (_, 'r') => '\r',
                    (_, 't') => '\t',
                    (_, '\\') => '\\',
                    &(_, c) if c == quote => quote,
                    &(end, c) => Err(SpannedError {
                        error: BadEscapeError(c),
                        location: (start, end),
                    })?,
                };
                chars.next();
                string.push(c);
            }
            c => string.push(c),
        }
    }
    Ok(string.into())
}

#[derive(Debug, thiserror::Error)]
#[error("unsupported escape sequence `\\{0}`")]
pub struct BadEscapeError(char);

#[derive(Debug, thiserror::Error)]
pub enum NumberError {
    #[error("expected an integer here")]
    NotInt,
    #[error("can't parse this value as a number")]
    NotFloat,
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
        assert_eq!(result, Expr::Number(Number::Int(42)));
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
            Expr::Index(
                Box::new(Expr::Identity),
                Box::new(Expr::String("foo".into()))
            )
        );
    }

    #[test]
    fn test_parse_pipe() {
        let result = parse(". | .foo").unwrap();
        assert_eq!(
            result,
            Expr::Pipe(
                Box::new(Expr::Identity),
                Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("foo".into()))
                ))
            )
        );
    }

    #[test]
    fn test_simple_chained_access() {
        let result = parse(".user.name").unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("user".into()))
                )),
                Box::new(Expr::String("name".into()))
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
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("status".into())),
                    )
                ),
                (
                    Expr::String("error".into()),
                    Expr::IndexOpt(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("body".into())),
                        )),
                        Box::new(Expr::String("error".into()))
                    ),
                ),
                (
                    Expr::String("apps".into()),
                    Expr::IndexOpt(
                        Box::new(Expr::Index(
                            Box::new(Expr::IndexOpt(
                                Box::new(Expr::Index(
                                    Box::new(Expr::Identity),
                                    Box::new(Expr::String("body".into())),
                                )),
                                Box::new(Expr::String("data".into())),
                            )),
                            Box::new(Expr::String("project".into())),
                        )),
                        Box::new(Expr::String("supportedApps".into()))
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
                Box::new(Expr::Index(
                    Box::new(Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("response".into()))
                    )),
                    Box::new(Expr::String("data".into()))
                )),
                Box::new(Expr::Index(
                    Box::new(Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("user".into()))
                    )),
                    Box::new(Expr::String("name".into()))
                )),
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
                    Expr::Call("contains".into(), vec![Expr::String("string".into())]),
                ),
                (
                    Expr::String("count".into()),
                    Expr::Call("length".into(), vec![]),
                )
            ])
        );
    }

    #[test]
    fn test_arithmetic() {
        let result = parse("-6. - 1. >= 5").unwrap();
        assert_eq!(
            result,
            Expr::GreaterEqual(
                Box::new(Expr::Subtract(
                    Box::new(Expr::Negate(Box::new(Expr::Number(Number::Float(6.0))))),
                    Box::new(Expr::Number(Number::Float(1.0)))
                )),
                Box::new(Expr::Number(Number::Int(5)))
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
            Expr::Alternative(
                Box::new(Expr::Alternative(
                    Box::new(Expr::Or(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("username".into()))
                        )),
                        Box::new(Expr::And(
                            Box::new(Expr::Bool(true)),
                            Box::new(Expr::Bool(false)),
                        )),
                    )),
                    Box::new(Expr::Or(
                        Box::new(Expr::And(
                            Box::new(Expr::Index(
                                Box::new(Expr::Identity),
                                Box::new(Expr::String("user".into()))
                            )),
                            Box::new(Expr::Bool(false))
                        )),
                        Box::new(Expr::Bool(true))
                    )),
                )),
                Box::new(Expr::String("not available".into()))
            )
        );
    }

    #[test]
    fn test_slice_expressions() {
        let result = parse(".[1:3]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Box::new(Expr::Identity),
                Some(Box::new(Expr::Number(Number::Int(1)))),
                Some(Box::new(Expr::Number(Number::Int(3))))
            )
        );

        let result = parse(".[2:]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Box::new(Expr::Identity),
                Some(Box::new(Expr::Number(Number::Int(2)))),
                None
            )
        );

        let result = parse(".[:5]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Box::new(Expr::Identity),
                None,
                Some(Box::new(Expr::Number(Number::Int(5))))
            )
        );

        let result = parse(".[:]").unwrap();
        assert_eq!(result, Expr::Slice(Box::new(Expr::Identity), None, None));
    }

    #[test]
    fn test_chained_slice_expressions() {
        let result = parse(".data[1:3]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("data".into()))
                )),
                Some(Box::new(Expr::Number(Number::Int(1)))),
                Some(Box::new(Expr::Number(Number::Int(3))))
            )
        );

        let result = parse(".[length() - 2:]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Box::new(Expr::Identity),
                Some(Box::new(Expr::Subtract(
                    Box::new(Expr::Call("length", vec![])),
                    Box::new(Expr::Number(Number::Int(2)))
                ))),
                None
            )
        );
    }

    #[test]
    fn test_recursive_descent() {
        let result = parse("..").unwrap();
        assert_eq!(result, Expr::RecursiveDescent);

        let result = parse(".. | .name").unwrap();
        assert_eq!(
            result,
            Expr::Pipe(
                Box::new(Expr::RecursiveDescent),
                Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("name".into()))
                ))
            )
        );
    }

    #[test]
    fn test_comprehensive_operators() {
        let result = parse("1 + 2 * 3 - 4 / 5 % 6").unwrap();
        assert_eq!(
            result,
            Expr::Subtract(
                Box::new(Expr::Add(
                    Box::new(Expr::Number(Number::Int(1))),
                    Box::new(Expr::Multiply(
                        Box::new(Expr::Number(Number::Int(2))),
                        Box::new(Expr::Number(Number::Int(3)))
                    ))
                )),
                Box::new(Expr::Modulo(
                    Box::new(Expr::Divide(
                        Box::new(Expr::Number(Number::Int(4))),
                        Box::new(Expr::Number(Number::Int(5)))
                    )),
                    Box::new(Expr::Number(Number::Int(6)))
                ))
            )
        );

        let _result = parse("1 < 2 <= 3 > 4 >= 5 == 6 != 7").unwrap();

        let result = parse("true and false or null").unwrap();
        assert_eq!(
            result,
            Expr::Or(
                Box::new(Expr::And(
                    Box::new(Expr::Bool(true)),
                    Box::new(Expr::Bool(false))
                )),
                Box::new(Expr::Null)
            )
        );
    }

    #[test]
    fn test_complex_field_access() {
        let result = parse(".user.profile.settings.theme").unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Index(
                    Box::new(Expr::Index(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("user".into()))
                        )),
                        Box::new(Expr::String("profile".into()))
                    )),
                    Box::new(Expr::String("settings".into()))
                )),
                Box::new(Expr::String("theme".into()))
            )
        );

        let result = parse(".user?.profile.settings?.theme?").unwrap();
        assert_eq!(
            result,
            Expr::IndexOpt(
                Box::new(Expr::IndexOpt(
                    Box::new(Expr::Index(
                        Box::new(Expr::IndexOpt(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("user".into()))
                        )),
                        Box::new(Expr::String("profile".into()))
                    )),
                    Box::new(Expr::String("settings".into()))
                )),
                Box::new(Expr::String("theme".into()))
            )
        );
    }

    #[test]
    fn test_comprehensive_indexing() {
        let result = parse(".[0][1][2]").unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Index(
                    Box::new(Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::Number(Number::Int(0)))
                    )),
                    Box::new(Expr::Number(Number::Int(1)))
                )),
                Box::new(Expr::Number(Number::Int(2)))
            )
        );

        let result = parse(".users[0].name[0:3]").unwrap();
        assert_eq!(
            result,
            Expr::Slice(
                Box::new(Expr::Index(
                    Box::new(Expr::Index(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("users".into()))
                        )),
                        Box::new(Expr::Number(Number::Int(0)))
                    )),
                    Box::new(Expr::String("name".into()))
                )),
                Some(Box::new(Expr::Number(Number::Int(0)))),
                Some(Box::new(Expr::Number(Number::Int(3))))
            )
        );

        let result = parse(".[0]?[1]?.field?").unwrap();
        assert_eq!(
            result,
            Expr::IndexOpt(
                Box::new(Expr::IndexOpt(
                    Box::new(Expr::IndexOpt(
                        Box::new(Expr::Identity),
                        Box::new(Expr::Number(Number::Int(0)))
                    )),
                    Box::new(Expr::Number(Number::Int(1)))
                )),
                Box::new(Expr::String("field".into()))
            )
        );
    }

    #[test]
    fn test_comprehensive_slicing() {
        let test_cases = vec![
            (".[:]", Expr::Slice(Box::new(Expr::Identity), None, None)),
            (
                ".[1:]",
                Expr::Slice(
                    Box::new(Expr::Identity),
                    Some(Box::new(Expr::Number(Number::Int(1)))),
                    None,
                ),
            ),
            (
                ".[:5]",
                Expr::Slice(
                    Box::new(Expr::Identity),
                    None,
                    Some(Box::new(Expr::Number(Number::Int(5)))),
                ),
            ),
            (
                ".[1:5]",
                Expr::Slice(
                    Box::new(Expr::Identity),
                    Some(Box::new(Expr::Number(Number::Int(1)))),
                    Some(Box::new(Expr::Number(Number::Int(5)))),
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
                Box::new(Expr::Identity),
                Some(Box::new(Expr::Subtract(
                    Box::new(Expr::Call("length", vec![])),
                    Box::new(Expr::Number(Number::Int(1)))
                ))),
                Some(Box::new(Expr::Call("length", vec![])))
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
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("name".into()))
                    ),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("age".into()))
                    )
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
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("name".into()))
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
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("user".into()))
                    )
                ),
                (
                    Expr::String("full name".into()),
                    Expr::Index(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("user".into()))
                        )),
                        Box::new(Expr::String("full_name".into()))
                    )
                ),
                (
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("key-with-dashes".into()))
                    ),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("value".into()))
                    )
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
                            Expr::Index(
                                Box::new(Expr::Identity),
                                Box::new(Expr::String("name".into()))
                            )
                        ),
                        (
                            Expr::String("age".into()),
                            Expr::Index(
                                Box::new(Expr::Identity),
                                Box::new(Expr::String("age".into()))
                            )
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
                Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("name".into()))
                ),
                Expr::Add(
                    Box::new(Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("age".into()))
                    )),
                    Box::new(Expr::Number(Number::Int(1)))
                ),
                Expr::Call(
                    "length",
                    vec![Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("items".into()))
                    )]
                ),
                Expr::Object(vec![(
                    Expr::String("status".into()),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("active".into()))
                    )
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
                    Expr::Number(Number::Int(1)),
                    Expr::Number(Number::Int(2))
                ]),
                Expr::Array(vec![
                    Expr::Number(Number::Int(3)),
                    Expr::Number(Number::Int(4))
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
                Box::new(Expr::Pipe(
                    Box::new(Expr::Pipe(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("users".into()))
                        )),
                        Box::new(Expr::Call(
                            "map",
                            vec![Expr::Index(
                                Box::new(Expr::Identity),
                                Box::new(Expr::String("name".into()))
                            )]
                        ))
                    )),
                    Box::new(Expr::Call("sort", vec![]))
                )),
                Box::new(Expr::Slice(
                    Box::new(Expr::Identity),
                    Some(Box::new(Expr::Number(Number::Int(0)))),
                    Some(Box::new(Expr::Number(Number::Int(5))))
                ))
            )
        );

        let result = parse(".name // \"Unknown\" | length()").unwrap();
        assert_eq!(
            result,
            Expr::Pipe(
                Box::new(Expr::Alternative(
                    Box::new(Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("name".into()))
                    )),
                    Box::new(Expr::String("Unknown".into()))
                )),
                Box::new(Expr::Call("length", vec![]))
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
            ("42", Expr::Number(Number::Int(42))),
            ("3.14", Expr::Number(Number::Float(3.14))),
            ("0", Expr::Number(Number::Int(0))),
            ("0.5", Expr::Number(Number::Float(0.5))),
            (".5", Expr::Number(Number::Float(0.5))),
            ("1e10", Expr::Number(Number::Float(1e10))),
        ];

        for (input, expected) in positive_cases {
            let actual = parse(input).unwrap();
            assert_eq!(actual, expected, "Failed for input: {}", input);
        }

        let result = parse("-7").unwrap();
        assert_eq!(result, Expr::Negate(Box::new(Expr::Number(Number::Int(7)))));

        let result = parse("-3.14").unwrap();
        assert_eq!(
            result,
            Expr::Negate(Box::new(Expr::Number(Number::Float(3.14))))
        );

        let result = parse("1.5e-3").unwrap();
        assert_eq!(result, Expr::Number(Number::Float(1.5e-3)));
    }

    #[test]
    fn test_precedence() {
        let result = parse("1 + 2 * 3").unwrap();
        assert_eq!(
            result,
            Expr::Add(
                Box::new(Expr::Number(Number::Int(1))),
                Box::new(Expr::Multiply(
                    Box::new(Expr::Number(Number::Int(2))),
                    Box::new(Expr::Number(Number::Int(3)))
                ))
            )
        );

        let result = parse("(1 + 2) * 3").unwrap();
        assert_eq!(
            result,
            Expr::Multiply(
                Box::new(Expr::Add(
                    Box::new(Expr::Number(Number::Int(1))),
                    Box::new(Expr::Number(Number::Int(2)))
                )),
                Box::new(Expr::Number(Number::Int(3)))
            )
        );

        let result = parse(".user.age + 1").unwrap();
        assert_eq!(
            result,
            Expr::Add(
                Box::new(Expr::Index(
                    Box::new(Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("user".into()))
                    )),
                    Box::new(Expr::String("age".into()))
                )),
                Box::new(Expr::Number(Number::Int(1)))
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
                Box::new(Expr::Identity),
                Box::new(Expr::String("field-with-dashes".into()))
            )
        );

        let result = parse(r#"."field with spaces""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Identity),
                Box::new(Expr::String("field with spaces".into()))
            )
        );

        let result = parse(r#"."%@#$^&*()""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Identity),
                Box::new(Expr::String("%@#$^&*()".into()))
            )
        );

        let result = parse(r#"."field-with-dashes"?"#).unwrap();
        assert_eq!(
            result,
            Expr::IndexOpt(
                Box::new(Expr::Identity),
                Box::new(Expr::String("field-with-dashes".into()))
            )
        );

        let result = parse(r#".user"#).unwrap(); // This works
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Identity),
                Box::new(Expr::String("user".into()))
            )
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
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("value".into()))
                    )
                ),
                (
                    Expr::String("spaces in key".into()),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("other".into()))
                    )
                )
            ])
        );

        let result = parse(r#"{true: .yes, false: .no, null: .empty}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::Bool(true),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("yes".into()))
                    )
                ),
                (
                    Expr::Bool(false),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("no".into()))
                    )
                ),
                (
                    Expr::Null,
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("empty".into()))
                    )
                )
            ])
        );

        let result = parse(r#"{name: .user, "full-name": .user.name, true: .active}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::String("name".into()),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("user".into()))
                    )
                ),
                (
                    Expr::String("full-name".into()),
                    Expr::Index(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("user".into()))
                        )),
                        Box::new(Expr::String("name".into()))
                    )
                ),
                (
                    Expr::Bool(true),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("active".into()))
                    )
                )
            ])
        );
    }

    #[test]
    fn test_boolean_and_null_literal_field_access() {
        let result = parse(".true").unwrap();
        assert_eq!(
            result,
            Expr::Index(Box::new(Expr::Identity), Box::new(Expr::Bool(true)))
        );

        let result = parse(".false").unwrap();
        assert_eq!(
            result,
            Expr::Index(Box::new(Expr::Identity), Box::new(Expr::Bool(false)))
        );

        let result = parse(".null").unwrap();
        assert_eq!(
            result,
            Expr::Index(Box::new(Expr::Identity), Box::new(Expr::Null))
        );

        let result = parse(".data.true").unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("data".into()))
                )),
                Box::new(Expr::Bool(true))
            )
        );

        let result = parse(".config.false.enabled").unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Index(
                    Box::new(Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("config".into()))
                    )),
                    Box::new(Expr::Bool(false))
                )),
                Box::new(Expr::String("enabled".into()))
            )
        );

        let result = parse(".data.null?").unwrap();
        assert_eq!(
            result,
            Expr::IndexOpt(
                Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("data".into()))
                )),
                Box::new(Expr::Null)
            )
        );

        let result = parse(r#"{true: .yes, false: .no, null: .empty}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::Bool(true),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("yes".into()))
                    )
                ),
                (
                    Expr::Bool(false),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("no".into()))
                    )
                ),
                (
                    Expr::Null,
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("empty".into()))
                    )
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
                    Box::new(Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("response".into()))
                    )),
                    Box::new(Expr::String("data".into()))
                ),
                Expr::Number(Number::Int(123))
            )])
        );

        let result = parse("{ (.key1): .value1, (.key2): .value2 }").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("key1".into()))
                    ),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("value1".into()))
                    )
                ),
                (
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("key2".into()))
                    ),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("value2".into()))
                    )
                )
            ])
        );

        let result = parse(r#"{ (.prefix + "-" + .suffix): .result }"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![(
                Expr::Add(
                    Box::new(Expr::Add(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("prefix".into()))
                        )),
                        Box::new(Expr::String("-".into()))
                    )),
                    Box::new(Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("suffix".into()))
                    ))
                ),
                Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("result".into()))
                )
            )])
        );
    }

    #[test]
    fn test_chained_quoted_key_access() {
        let result = parse(r#".data."field-name""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("data".into()))
                )),
                Box::new(Expr::String("field-name".into()))
            )
        );

        let result = parse(r#".user."full-name".display"#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Index(
                    Box::new(Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("user".into()))
                    )),
                    Box::new(Expr::String("full-name".into()))
                )),
                Box::new(Expr::String("display".into()))
            )
        );

        let result = parse(r#".data."field-name"?"#).unwrap();
        assert_eq!(
            result,
            Expr::IndexOpt(
                Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("data".into()))
                )),
                Box::new(Expr::String("field-name".into()))
            )
        );

        let result = parse(r#".response."api-data"."user-info"."email-address""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Index(
                    Box::new(Expr::Index(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("response".into()))
                        )),
                        Box::new(Expr::String("api-data".into()))
                    )),
                    Box::new(Expr::String("user-info".into()))
                )),
                Box::new(Expr::String("email-address".into()))
            )
        );
    }

    #[test]
    fn test_edge_cases_quoted_keys() {
        let result = parse(r#"."""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(Box::new(Expr::Identity), Box::new(Expr::String("".into())))
        );

        let result = parse(r#"."\n\t\r""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Identity),
                Box::new(Expr::String("\n\t\r".into()))
            )
        );

        let result = parse(r#"."123""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Identity),
                Box::new(Expr::String("123".into()))
            )
        );

        let result = parse(r#".">>=""#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Identity),
                Box::new(Expr::String(">>=".into()))
            )
        );

        let result = parse(r#"{"true": .value}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![(
                Expr::String("true".into()),
                Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("value".into()))
                )
            )])
        );
    }

    #[test]
    fn test_comprehensive_quoted_key_features() {
        let result = parse(r#".api."user-data".profile.true."last-login".false"#).unwrap();
        assert_eq!(
            result,
            Expr::Index(
                Box::new(Expr::Index(
                    Box::new(Expr::Index(
                        Box::new(Expr::Index(
                            Box::new(Expr::Index(
                                Box::new(Expr::Index(
                                    Box::new(Expr::Identity),
                                    Box::new(Expr::String("api".into()))
                                )),
                                Box::new(Expr::String("user-data".into()))
                            )),
                            Box::new(Expr::String("profile".into()))
                        )),
                        Box::new(Expr::Bool(true))
                    )),
                    Box::new(Expr::String("last-login".into()))
                )),
                Box::new(Expr::Bool(false))
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
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("user".into()))
                    )
                ),
                (
                    Expr::String("full-name".into()),
                    Expr::Index(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("user".into()))
                        )),
                        Box::new(Expr::String("display-name".into()))
                    )
                ),
                (
                    Expr::Bool(true),
                    Expr::Index(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("settings".into()))
                        )),
                        Box::new(Expr::String("enabled".into()))
                    )
                ),
                (
                    Expr::Bool(false),
                    Expr::Index(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("settings".into()))
                        )),
                        Box::new(Expr::String("disabled".into()))
                    )
                ),
                (
                    Expr::Null,
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("empty".into()))
                    )
                ),
                (
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("computed".into()))
                    ),
                    Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("dynamic".into()))
                    )
                )
            ])
        );

        let result = parse(r#".data."user-info"?.true."settings"?.null?"#).unwrap();
        assert_eq!(
            result,
            Expr::IndexOpt(
                Box::new(Expr::IndexOpt(
                    Box::new(Expr::Index(
                        Box::new(Expr::IndexOpt(
                            Box::new(Expr::Index(
                                Box::new(Expr::Identity),
                                Box::new(Expr::String("data".into()))
                            )),
                            Box::new(Expr::String("user-info".into()))
                        )),
                        Box::new(Expr::Bool(true))
                    )),
                    Box::new(Expr::String("settings".into()))
                )),
                Box::new(Expr::Null)
            )
        );
    }

    #[test]
    fn test_unary_not_operator() {
        let result = parse("not true").unwrap();
        assert_eq!(result, Expr::Not(Box::new(Expr::Bool(true))));

        let result = parse("not false").unwrap();
        assert_eq!(result, Expr::Not(Box::new(Expr::Bool(false))));

        let result = parse("not null").unwrap();
        assert_eq!(result, Expr::Not(Box::new(Expr::Null)));

        let result = parse("not .active").unwrap();
        assert_eq!(
            result,
            Expr::Not(Box::new(Expr::Index(
                Box::new(Expr::Identity),
                Box::new(Expr::String("active".into()))
            )))
        );

        let result = parse("not not true").unwrap();
        assert_eq!(
            result,
            Expr::Not(Box::new(Expr::Not(Box::new(Expr::Bool(true)))))
        );

        let result = parse("not (.age > 18)").unwrap();
        assert_eq!(
            result,
            Expr::Not(Box::new(Expr::Greater(
                Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("age".into()))
                )),
                Box::new(Expr::Number(Number::Int(18)))
            )))
        );

        let result = parse("not .active and .verified").unwrap();
        assert_eq!(
            result,
            Expr::And(
                Box::new(Expr::Not(Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("active".into()))
                )))),
                Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("verified".into()))
                ))
            )
        );

        let result = parse("not true and false").unwrap();
        assert_eq!(
            result,
            Expr::And(
                Box::new(Expr::Not(Box::new(Expr::Bool(true)))),
                Box::new(Expr::Bool(false))
            )
        );

        let result = parse("not true or false").unwrap();
        assert_eq!(
            result,
            Expr::Or(
                Box::new(Expr::Not(Box::new(Expr::Bool(true)))),
                Box::new(Expr::Bool(false))
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
                Expr::String("name".into())
            )])
        );

        let result = parse("{name, age, active}").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (Expr::String("name".into()), Expr::String("name".into())),
                (Expr::String("age".into()), Expr::String("age".into())),
                (Expr::String("active".into()), Expr::String("active".into()))
            ])
        );

        let result = parse("{name, age: .user.age, active}").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (Expr::String("name".into()), Expr::String("name".into())),
                (
                    Expr::String("age".into()),
                    Expr::Index(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("user".into()))
                        )),
                        Box::new(Expr::String("age".into()))
                    )
                ),
                (Expr::String("active".into()), Expr::String("active".into()))
            ])
        );

        let result = parse(r#"{"user-name"}"#).unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![(
                Expr::String("user-name".into()),
                Expr::String("user-name".into())
            )])
        );

        let result = parse("{true, false, null}").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (Expr::Bool(true), Expr::Bool(true)),
                (Expr::Bool(false), Expr::Bool(false)),
                (Expr::Null, Expr::Null)
            ])
        );

        let result =
            parse(r#"{name, "full-name": .user.name, active, count: length(.items), verified}"#)
                .unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (Expr::String("name".into()), Expr::String("name".into())),
                (
                    Expr::String("full-name".into()),
                    Expr::Index(
                        Box::new(Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("user".into()))
                        )),
                        Box::new(Expr::String("name".into()))
                    )
                ),
                (Expr::String("active".into()), Expr::String("active".into())),
                (
                    Expr::String("count".into()),
                    Expr::Call(
                        "length",
                        vec![Expr::Index(
                            Box::new(Expr::Identity),
                            Box::new(Expr::String("items".into()))
                        )]
                    )
                ),
                (
                    Expr::String("verified".into()),
                    Expr::String("verified".into())
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
                        (Expr::String("name".into()), Expr::String("name".into())),
                        (Expr::String("age".into()), Expr::String("age".into()))
                    ])
                ),
                (
                    Expr::String("settings".into()),
                    Expr::Object(vec![(
                        Expr::String("theme".into()),
                        Expr::String("theme".into())
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
            Expr::Not(Box::new(Expr::Negate(Box::new(Expr::Number(Number::Int(
                5
            ))))))
        );

        let result = parse("-not true").unwrap();
        assert_eq!(
            result,
            Expr::Negate(Box::new(Expr::Not(Box::new(Expr::Bool(true)))))
        );

        let result = parse("-(not true)").unwrap();
        assert_eq!(
            result,
            Expr::Negate(Box::new(Expr::Not(Box::new(Expr::Bool(true)))))
        );

        let result = parse("not (-5)").unwrap();
        assert_eq!(
            result,
            Expr::Not(Box::new(Expr::Negate(Box::new(Expr::Number(Number::Int(
                5
            ))))))
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
                Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("dynamic".into()))
                ),
                Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("value".into()))
                )
            )])
        );

        let result = parse("{}").unwrap();
        assert_eq!(result, Expr::Object(vec![]));

        let result = parse("{name, age}").unwrap();
        assert_eq!(
            result,
            Expr::Object(vec![
                (Expr::String("name".into()), Expr::String("name".into())),
                (Expr::String("age".into()), Expr::String("age".into()))
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
                Box::new(Expr::Bool(true)),
                Box::new(Expr::Not(Box::new(Expr::Bool(false))))
            )
        );

        let result = parse("not true or false").unwrap();
        assert_eq!(
            result,
            Expr::Or(
                Box::new(Expr::Not(Box::new(Expr::Bool(true)))),
                Box::new(Expr::Bool(false))
            )
        );

        let result = parse("not -5 + 3").unwrap();
        assert_eq!(
            result,
            Expr::Add(
                Box::new(Expr::Not(Box::new(Expr::Negate(Box::new(Expr::Number(
                    Number::Int(5)
                )))))),
                Box::new(Expr::Number(Number::Int(3)))
            )
        );

        let result = parse(".active | not .disabled").unwrap();
        assert_eq!(
            result,
            Expr::Pipe(
                Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("active".into()))
                )),
                Box::new(Expr::Not(Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("disabled".into()))
                ))))
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
                    Expr::Not(Box::new(Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("disabled".into()))
                    )))
                ),
                (Expr::String("name".into()), Expr::String("name".into())),
                (
                    Expr::String("verified".into()),
                    Expr::Not(Box::new(Expr::Not(Box::new(Expr::Index(
                        Box::new(Expr::Identity),
                        Box::new(Expr::String("checked".into()))
                    )))))
                )
            ])
        );

        let result = parse(".users | map({name, active: not .disabled})").unwrap();
        assert_eq!(
            result,
            Expr::Pipe(
                Box::new(Expr::Index(
                    Box::new(Expr::Identity),
                    Box::new(Expr::String("users".into()))
                )),
                Box::new(Expr::Call(
                    "map",
                    vec![Expr::Object(vec![
                        (Expr::String("name".into()), Expr::String("name".into())),
                        (
                            Expr::String("active".into()),
                            Expr::Not(Box::new(Expr::Index(
                                Box::new(Expr::Identity),
                                Box::new(Expr::String("disabled".into()))
                            )))
                        )
                    ])]
                ))
            )
        );
    }

    #[test]
    fn test_double_negation() {
        let result = parse("- -5").unwrap();
        assert_eq!(
            result,
            Expr::Negate(Box::new(Expr::Negate(Box::new(Expr::Number(Number::Int(
                5
            ))))))
        );

        let result = parse("- - -42").unwrap();
        assert_eq!(
            result,
            Expr::Negate(Box::new(Expr::Negate(Box::new(Expr::Negate(Box::new(
                Expr::Number(Number::Int(42))
            ))))))
        );

        let result = parse("1 + - -3").unwrap();
        assert_eq!(
            result,
            Expr::Add(
                Box::new(Expr::Number(Number::Int(1))),
                Box::new(Expr::Negate(Box::new(Expr::Negate(Box::new(
                    Expr::Number(Number::Int(3))
                )))))
            )
        );

        let result = parse("-(- 7)").unwrap();
        assert_eq!(
            result,
            Expr::Negate(Box::new(Expr::Negate(Box::new(Expr::Number(Number::Int(
                7
            ))))))
        );
    }
}
