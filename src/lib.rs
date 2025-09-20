// Copyright (c) 2025 Lina Butler
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! # `jqish`: A `jq`-like expression evaluator
//!
//! `jqish` is a library that implements a subset of the [`jq` language](https://jqlang.org/manual)
//! for querying and transforming JSON-like data structures in a Rust program.

pub mod error;
pub mod lexer;
pub mod parser;

pub use parser::{Expr, parse};
