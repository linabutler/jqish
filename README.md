# jqish: A `jq`-like expression parser

`jqish` implements a subset of the [`jq` language](https://jqlang.org/manual) for querying and transforming JSON-like data.

While the venerable `jq` is a command-line tool that operates on JSON text, `jqish` is a library that operates on data structures in your program. Think of it like an alternative to [JSONPath](https://www.rfc-editor.org/rfc/rfc9535) or [JSON Pointer](https://www.rfc-editor.org/rfc/rfc6901).

🚧 This project is still **under development**. There's a grammar and parser, but no evaluator yet.

## Usage

Add `jqish` to your project's `Cargo.toml`:

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

### ✅ Supported

These features parse as described in the [`jq` manual](https://jqlang.org/manual/).

### Filters

|                             |                                                                |
|-----------------------------|----------------------------------------------------------------|
| Identity                    | `.`                                                            |
| Object identifier-indexing  | `.foo`, `.foo.bar`, `."foo-bar"`                               |
| Array and object indexing   | `.[0]`, `.["key"]`, `.[.expr]`                                 |
| Array slicing               | `.[1:3]`, `.[2:]`, `.[:5]`, `.[:]`, `.[-3]`, `.[length() % 2]` |
| Optionals                   | `.foo?`, `."foo-bar".baz?`, `.[1]?`                            |


### Types and values

|                        |                                                                                                                           |
|------------------------|---------------------------------------------------------------------------------------------------------------------------|
| Numbers                | `42`, `-10`, `3.14`, `-1e10`, `1.5e-3`                                                                                    |
| Strings                | `"hello"`, `'good-bye'`, `"with \"escapes\""`                                                                             |
| Literals               | `true`, `false`, `null`                                                                                                   |
| Array construction     | `[]`, `[1, 2, 3]`, `[.a, .b, .c | .d]`                                                                                    |
| Object construction    | `{}`, `{hello: "world"}`, `{name: .user, age, "favorite-name": .color}`, `{(.key): .value, (.prefix + .suffix): .result}` |


### Expressions and operators

|                        |                                  |
|------------------------|----------------------------------|
| Pipes                  | `.a | .b`                        |
| Arithmetic operations  | `+`, `-`, `*`, `/`, `%`          |
| Comparisons            | `==`, `!=`, `<`, `>`, `<=`, `>=` |
| Boolean operators      | `a and b`, `a or b`, `not b`     |
| Alternatives           | `a // b`                         |
| Grouping               | `(. + 2) * 5`                    |


### ❌ Not supported

Because `jqish` is designed to be embedded in a larger Rust program, it's missing some of `jq`'s advanced features.

* **Iterators** and **generators**, including recursive descent: `.[]`, `.foo[]`, `.. | .a?`. Since a `jqish` expression can only return a single result, there's no way to represent the output of an iterator, generator, or recursive descent.
* **Control flow**: `if-then-else`, `while`, `try-catch`, and recursion. You can write more complex transformations that need these constructs in Rust.
* **Variables**, including assignment operators: `... as $ident`
* **Destructuring alternatives**, because these require variables to work: `.[] as {$a, $b, c: {$d, $e}} ?// {$a, $b, c: [{$d, $e}]} | {$a, $b, $d, $e}`
* **String interpolation**: `"Hello \(name)"`
* Defining **functions**
* Modules
* Comments

## License

`jqish` is distributed under the terms of either the MIT license or the Apache 2.0 license.

The `jqish` language is based on the syntax and semantics of `jq`, which is distributed under the [MIT license](https://github.com/jqlang/jq/blob/master/COPYING).
