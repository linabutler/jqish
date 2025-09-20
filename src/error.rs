// Copyright (c) 2025 Lina Butler
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::parser::{BadEscapeError, NumberError};

/// An error that includes source location information.
#[derive(Debug, thiserror::Error)]
#[error("{error} at {}-{}", .location.0, .location.1.saturating_sub(1))]
pub struct SpannedError<T> {
    /// The underlying error.
    pub error: T,

    /// The `[start, end)` byte offsets in the input where the error occurred.
    pub location: (usize, usize),
}

impl<T> SpannedError<T> {
    pub fn map<U>(self, transform: impl FnOnce(T) -> U) -> SpannedError<U> {
        SpannedError {
            error: transform(self.error),
            location: self.location,
        }
    }
}

/// The error type returned when a `jqish` expression fails to parse.
#[derive(Debug, thiserror::Error)]
pub enum LexicalError {
    #[error("`{0}` can't be used here")]
    Unexpected(char),
    #[error("unterminated string; did you forget a closing `\"`?")]
    UnterminatedString,
    #[error(transparent)]
    BadEscape(#[from] BadEscapeError),
    #[error(transparent)]
    NotNumber(#[from] NumberError),
    #[error("this expression is invalid")]
    BadToken,
}
