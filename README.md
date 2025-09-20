# `jqish`: A `jq`-like expression evaluator

`jqish` is a Rust library that implements a subset of the [`jq` language](https://jqlang.org/manual) for querying and transforming JSON-like data. While `jq` is a full-featured command-line tool, `jqish` is meant to be embedded in a larger program: think of it as a complement to [JSONPath](https://www.rfc-editor.org/rfc/rfc9535) for working with in-memory data structures in your program, rather than `sed` for JSON text.

## Usage

Add `jqish` to your program's `Cargo.toml`:

```toml
[dependencies]
jqish = "0.1"
```

### Quick Start

```rust
use jqish::{parse, Expr};

// Parse a simple object property access.
let expr = parse(".name").unwrap();
println!("{:?}", expr); // Expr::Index(...)

// Parse an expression that constructs an object.
let expr = parse("{name, age: .user.age, active}").unwrap();
println!("{:?}", expr); // Expr::Object([...])

// Parse a more complex expression.
let expr = parse("not (.foo | .bar // .baz)").unwrap();
println!("{:?}", expr); // Expr::Not(...)
```

## Grammar comparison

Because `jqish` is designed to be embedded, it's missing some of `jq`'s advanced features. `jqish` focuses on querying data structures, and leaves the more powerful transformations to your program.

### ✅ **Supported**

### Filters

* **Identity**: `.`.
* **Identifier-based indexing**: `.foo`, `.foo.bar`, `."foo-bar"`
* **Array and object indexing**: `.[0]`, `.["key"]`, `.[.expr]`
* **Array slicing**: `.[1:3]`, `.[2:]`, `.[:5]`, `.[:]`, `.[-3]`, `.[length() % 2]`
* **Optional indexing**: `.foo?`, `."foo-bar".baz?`, `.[1]?`

### Literals and types

* **Numbers**: `42`, `-10`, `3.14`, `-1e10`, `1.5e-3`
* **Strings**: `"hello"`, `"with \\"escapes\\""`
* **Booleans**: `true`, `false`
* **Arrays and objects**: `[]`, `[1, 2, 3]`, `{}`, `{hello: "world"}`
* `null`

### Expressions and operators

* **Pipes**: `.a | .b`
* **Arithmetic operations**: `+`, `-`, `*`, `/`, `%`
* **Comparisons**: `==`, `!=`, `<`, `>`, `<=`, `>=`
* **Boolean operators**: `a and b`, `a or b`, `not b`
* **Alternatives**: `a // b`
* **Grouping**: `(. + 2) * 5`

### Array and object construction

* **Array construction**: `[.a, .b, .c | .d]`
* **Object construction**: `{name: .user, age, "favorite-name": .color}`
* **Computed keys**: `{(.key): .value, (.prefix + .suffix): .result}`
* **Recursive descent**: `..`

### ❌ **Not supported**

A `jqish` pipeline works on data that's already in your program, and maps one value to another value, so the `jqish` grammar doesn't support streaming operations (iterators, generators) or programming language features (variables, control flow, modules, comments, defining custom functions).

* **Iterators**: `.[]`, `.foo[]`.
* **Generators**
* **Control flow**: `if-then-else`, `while`, `try-catch`
* **Variables**, including assignment: `... as $ident`
* **Destructuring alternatives**: `.[] as {$a, $b, c: {$d, $e}} ?// {$a, $b, c: [{$d, $e}]} | {$a, $b, $d, $e}`
* **Recursion**
* **String interpolation**: `"Hello \(name)"`
* **Defining functions**
* **Modules**
* **Comments**

## License

`jqish` is distributed under the terms of either the MIT license or the Apache 2.0 license.

The `jqish` language is based on the syntax and semantics of `jq`, which is distributed under the [MIT license](https://github.com/jqlang/jq/blob/master/COPYING).
