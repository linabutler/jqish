use std::fmt::Display;

use allocative::Allocative;
use once_cell::sync::OnceCell;
use starlark::{
    ErrorKind,
    any::ProvidesStaticType,
    const_frozen_string,
    environment::{
        FrozenModule, GlobalsBuilder, LibraryExtension, Methods, MethodsBuilder, MethodsStatic,
        Module,
    },
    eval::Evaluator,
    starlark_module,
    syntax::{AstModule, Dialect},
    values::{
        AllocValue, FrozenStringValue, FrozenValue, Heap, NoSerialize, OwnedFrozenValue,
        StarlarkValue, StringValue, Trace, Tracer, Value, list::AllocList, none::NoneOr,
        starlark_value, typing::StarlarkCallable,
    },
};

use crate::parser::{Expr, Number};

const SOURCE: &str = include_str!("./eval.star");

pub struct FilterExprEvaluator(OnceCell<FrozenModule>);

impl FilterExprEvaluator {
    pub const fn new() -> Self {
        Self(OnceCell::new())
    }

    pub fn get(&self) -> OwnedFrozenValue {
        self.module().unwrap().get("eval").unwrap()
    }

    fn module(&self) -> Result<&FrozenModule, starlark::Error> {
        self.0.get_or_try_init(|| {
            let module = Module::new();
            let ast = AstModule::parse("<jqish>", SOURCE.to_owned(), &Dialect::Standard)?;
            {
                let mut eval = Evaluator::new(&module);
                let globals =
                    GlobalsBuilder::extended_by(&[LibraryExtension::Print, LibraryExtension::Json])
                        .with(globals)
                        .build();
                eval.eval_module(ast, &globals)?;
            }
            Ok(module.freeze()?)
        })
    }
}

#[starlark_module]
fn globals(b: &mut GlobalsBuilder) {
    /// Indexes into a value.
    fn index<'v>(target: Value<'v>, at: Value<'v>, heap: &'v Heap) -> starlark::Result<Value<'v>> {
        Ok(target.at(at, heap).unwrap_or_else(|_| {
            if let Some(name) = at.unpack_str()
                && let Ok(Some(attribute)) = target.get_attr(name, heap)
            {
                attribute
            } else {
                Value::new_none()
            }
        }))
    }

    /// Executes a function `f`, suppressing any errors.
    /// This is used to evaluate `?` expressions.
    fn try_<'v>(
        f: StarlarkCallable<'v, (), FrozenValue>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> starlark::Result<Value<'v>> {
        Ok(match eval.eval_function(f.0, &[], &[]) {
            Ok(value) => value,
            Err(err) => match err.into_kind() {
                ErrorKind::Fail(err) => Err(starlark::Error::new_kind(ErrorKind::Fail(err)))?,
                _ => Value::new_none(),
            },
        })
    }
}

#[derive(Allocative, Clone, Copy, Debug, NoSerialize, ProvidesStaticType)]
#[allocative(skip)]
pub struct FilterExpr<'v>(pub &'v Expr);

impl<'v> AllocValue<'v> for FilterExpr<'v> {
    fn alloc_value(self, heap: &'v Heap) -> Value<'v> {
        heap.alloc_complex_no_freeze(self)
    }
}

unsafe impl<'v> Trace<'v> for FilterExpr<'v> {
    fn trace(&mut self, _tracer: &Tracer<'v>) {
        // ...
    }
}

impl Display for FilterExpr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "filter.Expr")
    }
}

#[starlark_value(type = "filter.Expr", StarlarkTypeRepr, UnpackValue)]
impl<'v> StarlarkValue<'v> for FilterExpr<'v> {
    fn get_methods() -> Option<&'static Methods> {
        #[starlark_module]
        fn methods(builder: &mut MethodsBuilder) {
            #[starlark(attribute, speculative_exec_safe)]
            fn r#type<'v>(
                this: &'v FilterExpr<'v>,
                _heap: &'v Heap,
            ) -> starlark::Result<FrozenStringValue> {
                Ok(match &this.0 {
                    Expr::Identity => const_frozen_string!("id"),
                    Expr::Number(_) => const_frozen_string!("number"),
                    Expr::String(_) => const_frozen_string!("string"),
                    Expr::Bool(_) => const_frozen_string!("bool"),
                    Expr::Null => const_frozen_string!("null"),
                    Expr::Pipe(..) => const_frozen_string!("pipe"),
                    Expr::Add(..) => const_frozen_string!("add"),
                    Expr::Subtract(..) => const_frozen_string!("sub"),
                    Expr::Multiply(..) => const_frozen_string!("mul"),
                    Expr::Divide(..) => const_frozen_string!("div"),
                    Expr::Modulo(..) => const_frozen_string!("mod"),
                    Expr::Index(..) => const_frozen_string!("index"),
                    Expr::Slice(..) => const_frozen_string!("slice"),
                    Expr::Object(..) => const_frozen_string!("object"),
                    Expr::Array(..) => const_frozen_string!("array"),
                    Expr::Call(..) => const_frozen_string!("call"),
                    Expr::Or(..) => const_frozen_string!("or"),
                    Expr::And(..) => const_frozen_string!("and"),
                    Expr::Not(..) => const_frozen_string!("not"),
                    Expr::Opt(..) => const_frozen_string!("opt"),
                    Expr::Alternative(..) => const_frozen_string!("alt"),
                    Expr::Equal(..) => const_frozen_string!("eq"),
                    Expr::NotEqual(..) => const_frozen_string!("ne"),
                    Expr::Less(..) => const_frozen_string!("lt"),
                    Expr::Greater(..) => const_frozen_string!("gt"),
                    Expr::LessEqual(..) => const_frozen_string!("le"),
                    Expr::GreaterEqual(..) => const_frozen_string!("ge"),
                    Expr::Negate(_) => const_frozen_string!("neg"),
                })
            }

            #[starlark(attribute, speculative_exec_safe)]
            fn value<'v>(this: &'v FilterExpr<'v>, heap: &'v Heap) -> starlark::Result<Value<'v>> {
                Ok(match &this.0 {
                    Expr::Number(Number::Float(f)) => heap.alloc(*f),
                    Expr::Number(Number::Int(n)) => heap.alloc(*n),
                    Expr::String(s) => heap.alloc_str(s).to_value(),
                    &Expr::Bool(b) => Value::new_bool(*b),
                    Expr::Null => Value::new_none(),
                    _ => return Err(starlark::Error::new_native(EvalError::NoValue)),
                })
            }

            #[starlark(attribute, speculative_exec_safe)]
            fn lhs<'v>(this: &'v FilterExpr<'v>) -> starlark::Result<FilterExpr<'v>> {
                Ok(match &this.0 {
                    Expr::Pipe(lhs, _) => FilterExpr(lhs),
                    Expr::Add(lhs, _) => FilterExpr(lhs),
                    Expr::Subtract(lhs, _) => FilterExpr(lhs),
                    Expr::Multiply(lhs, _) => FilterExpr(lhs),
                    Expr::Divide(lhs, _) => FilterExpr(lhs),
                    Expr::Modulo(lhs, _) => FilterExpr(lhs),
                    Expr::Or(lhs, _) => FilterExpr(lhs),
                    Expr::And(lhs, _) => FilterExpr(lhs),
                    Expr::Alternative(lhs, _) => FilterExpr(lhs),
                    Expr::Equal(lhs, _) => FilterExpr(lhs),
                    Expr::NotEqual(lhs, _) => FilterExpr(lhs),
                    Expr::Less(lhs, _) => FilterExpr(lhs),
                    Expr::Greater(lhs, _) => FilterExpr(lhs),
                    Expr::LessEqual(lhs, _) => FilterExpr(lhs),
                    Expr::GreaterEqual(lhs, _) => FilterExpr(lhs),
                    Expr::Opt(expr) => FilterExpr(expr),
                    _ => return Err(starlark::Error::new_native(EvalError::NoLhs)),
                })
            }

            #[starlark(attribute, speculative_exec_safe)]
            fn rhs<'v>(this: &'v FilterExpr<'v>) -> starlark::Result<FilterExpr<'v>> {
                Ok(match &this.0 {
                    Expr::Pipe(_, rhs) => FilterExpr(rhs),
                    Expr::Add(_, rhs) => FilterExpr(rhs),
                    Expr::Subtract(_, rhs) => FilterExpr(rhs),
                    Expr::Multiply(_, rhs) => FilterExpr(rhs),
                    Expr::Divide(_, rhs) => FilterExpr(rhs),
                    Expr::Modulo(_, rhs) => FilterExpr(rhs),
                    Expr::Or(_, rhs) => FilterExpr(rhs),
                    Expr::And(_, rhs) => FilterExpr(rhs),
                    Expr::Alternative(_, rhs) => FilterExpr(rhs),
                    Expr::Equal(_, rhs) => FilterExpr(rhs),
                    Expr::NotEqual(_, rhs) => FilterExpr(rhs),
                    Expr::Less(_, rhs) => FilterExpr(rhs),
                    Expr::Greater(_, rhs) => FilterExpr(rhs),
                    Expr::LessEqual(_, rhs) => FilterExpr(rhs),
                    Expr::GreaterEqual(_, rhs) => FilterExpr(rhs),
                    Expr::Not(expr) => FilterExpr(expr),
                    Expr::Negate(expr) => FilterExpr(expr),
                    _ => return Err(starlark::Error::new_native(EvalError::NoRhs)),
                })
            }

            #[starlark(attribute, speculative_exec_safe)]
            fn call<'v>(
                this: &'v FilterExpr<'v>,
                heap: &'v Heap,
            ) -> starlark::Result<(StringValue<'v>, Vec<FilterExpr<'v>>)> {
                Ok(match &this.0 {
                    Expr::Call(name, args) => (
                        heap.alloc_str_intern(name),
                        args.iter().map(FilterExpr).collect(),
                    ),
                    _ => return Err(starlark::Error::new_native(EvalError::NotCall)),
                })
            }

            #[starlark(attribute, speculative_exec_safe)]
            fn members<'v>(
                this: &'v FilterExpr<'v>,
                heap: &'v Heap,
            ) -> starlark::Result<Value<'v>> {
                Ok(match &this.0 {
                    Expr::Object(pairs) => heap.alloc(AllocList(
                        pairs
                            .iter()
                            .map(|(key, value)| (FilterExpr(key), FilterExpr(value))),
                    )),
                    Expr::Array(items) => heap.alloc(AllocList(items.iter().map(FilterExpr))),
                    _ => return Err(starlark::Error::new_native(EvalError::NoMembers)),
                })
            }

            #[starlark(attribute, speculative_exec_safe)]
            fn index<'v>(
                this: &'v FilterExpr<'v>,
            ) -> starlark::Result<(FilterExpr<'v>, FilterExpr<'v>)> {
                Ok(match &this.0 {
                    Expr::Index(target, index) => (FilterExpr(target), FilterExpr(index)),
                    _ => return Err(starlark::Error::new_native(EvalError::NotIndexable)),
                })
            }

            #[starlark(attribute, speculative_exec_safe)]
            fn slice<'v>(
                this: &'v FilterExpr<'v>,
            ) -> starlark::Result<(
                FilterExpr<'v>,
                NoneOr<FilterExpr<'v>>,
                NoneOr<FilterExpr<'v>>,
            )> {
                Ok(match &this.0 {
                    Expr::Slice(expr, start, end) => (
                        FilterExpr(expr),
                        NoneOr::from_option(start.as_deref().map(FilterExpr)),
                        NoneOr::from_option(end.as_deref().map(FilterExpr)),
                    ),
                    _ => return Err(starlark::Error::new_native(EvalError::NotSlice)),
                })
            }
        }
        static SELF: MethodsStatic = MethodsStatic::new();
        SELF.methods(methods)
    }
}

#[derive(Debug, thiserror::Error)]
pub enum EvalError {
    #[error("expression doesn't have a value")]
    NoValue,
    #[error("expression doesn't have a lhs-hand side")]
    NoLhs,
    #[error("expression doesn't have a rhs-hand side")]
    NoRhs,
    #[error("expression doesn't have members")]
    NoMembers,
    #[error("not indexable")]
    NotIndexable,
    #[error("not a call expression")]
    NotCall,
    #[error("not a slice expression")]
    NotSlice,
}
