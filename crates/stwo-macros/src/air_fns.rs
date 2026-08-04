//! `define_air_fns!`: the felt-to-AIR compiler front end
//! (docs/felt-air-compiler.md).
//!
//! Functions written as felt code compile to AIR components: each function
//! is a table, each activation a row. The calling convention is a LogUp
//! relation per function over the tuple `(inputs..., outputs...)` — a row
//! consumes its own activation tuple and emits one for every call it makes;
//! the public side emits the entry activations. `inline fn`s are
//! frame-spliced sub-circuits instead (no table, no activation).
//!
//! The maximum constraint degree is a compile parameter: multiplicative
//! chains that would breach it are unrolled into materialized intermediate
//! columns (one equality constraint each, deduplicated by common
//! subexpression), while additive chains stay inline. `for` loops with
//! constant bounds unroll; fixed-size arrays (`state: [felt; 16]`
//! parameters, constant indexing, `map`/`sum`/`update` builders) flatten to
//! scalars at compile time, so the whole body lowers to single-assignment
//! felt cells — a write-once frame.
//!
//! The lowering targets the `define_trace_tables!` backend — tables,
//! generic column structs, and the exported lookup macros — so AIR
//! evaluation and interaction-trace generation are shared with the rest of
//! the system. The witness side is the same program run concretely: the
//! generated `call_<fn>` executes the lowered cells over `BaseField`
//! values, recursively activates callees, and pushes the rows.

use std::collections::HashMap;

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{ToTokens, format_ident, quote};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{Expr, Ident, LitStr, Path, Token, braced, bracketed, parenthesized, parse_macro_input};

use crate::trace_tables::{
    LookupsDef, OpcodeDef, column_struct_name, const_eval, count_opcode_flags,
    generate_prover_columns, generate_table, table_name,
};

fn to_pascal_case(s: &str) -> String {
    s.split('_')
        .map(|word| {
            let mut chars = word.chars();
            match chars.next() {
                None => String::new(),
                Some(first) => first.to_ascii_uppercase().to_string() + chars.as_str(),
            }
        })
        .collect()
}

// =============================================================================
// Parsing
// =============================================================================

/// A function parameter: a scalar felt or a fixed-size array of felts.
struct Param {
    name: Ident,
    size: Option<usize>,
}

/// One statement of a function body.
enum FnStmt {
    /// `let x = expr;` — any felt/array expression (including `map`, `sum`,
    /// `update`, array literals, and calls).
    Let { names: Vec<Ident>, value: Expr },
    /// `assert lhs == rhs;`
    Assert { lhs: Expr, rhs: Expr },
    /// `for i in a..b { ... }` — unrolled at compile time.
    For {
        var: Ident,
        start: usize,
        end: usize,
        body: Vec<FnStmt>,
    },
    /// `emit r(args);` / `consume r(args);` — a row's contribution to an
    /// externally declared relation `r` (declared `relation r(arity);` at
    /// the top of the macro). `emit` adds `+mult / combine(args)`, `consume`
    /// adds `-mult / ...`, where `mult` defaults to `enabler` but may be
    /// overridden by `emit(expr) r(args)` / `consume(expr) r(args)` for
    /// flag-gated lookups (e.g. `consume(is_bitwise) bitwise(...)`). The
    /// relation balances across the whole proof, like the per-function io
    /// activation tuples.
    Relation {
        relation: Ident,
        args: Vec<Expr>,
        emit: bool,
        /// Multiplicity expression; `None` means `enabler`.
        mult: Option<Expr>,
    },
    /// `hint name = expr;` — a prover-chosen committed column, free in the
    /// AIR (the body constrains it with `assert`s), filled by evaluating
    /// `expr` concretely. Opcodes use this for witness columns that are not
    /// in-row derivations (carries, sign decompositions, inverse markers).
    Hint { name: Ident, expr: Expr },
    /// `constrain expr;` — asserts `expr == 0` **without** the implicit
    /// enabler gate that `assert` adds. For constraints already gated by an
    /// opcode flag (e.g. `flag * carry * (1 - carry)`), where multiplying by
    /// enabler too would breach the degree budget; the flag zeroes the
    /// constraint on padding rows.
    Constrain { expr: Expr },
}

struct AirFn {
    inline: bool,
    name: Ident,
    params: Vec<Param>,
    body: Vec<FnStmt>,
    rets: Vec<Expr>,
}

struct AirFnsInput {
    max_degree: usize,
    /// Embedded mode: generate only the table, the columns struct with its
    /// straight-line `evaluation()`, and the row-fill function — the host
    /// system provides relations, components, and proving. The idents are
    /// flag columns appended to the table (booleanity and emission gating
    /// are the host component's business). Returns are materialized so the
    /// activation tuple is degree 1 (host relations may pair entries).
    embedded: Option<Vec<Ident>>,
    /// When set with `embedded`, also emit the narrow/wide/io LogUp component
    /// adapter wired to `crate::relations::Relations`.
    embedded_component: bool,
    /// Whether the generated component enforces booleanity of its committed
    /// enabler column. Trusted schedules can disable this when an explicit
    /// equality binds the enabler to a boolean preprocessed row mask.
    embedded_enabler_boolean: bool,
    /// Relation bundle used by a generated embedded component. The default is
    /// the zkVM prover bundle; recursion supplies a bundle containing the exact
    /// shared relation instances used by its universal registry.
    embedded_relations: Path,
    /// Number of adjacent LogUp fractions combined in one interaction column
    /// for generated embedded components.
    logup_batch: usize,
    /// Whether the embedded component also exposes named-relation evaluation
    /// for compilation into another AIR.
    embedded_dynamic_component: bool,
    /// Trusted preprocessed columns used instead of committed trace columns by
    /// a generated embedded component. Each name identifies a function
    /// parameter and each string is its framework preprocessed-column ID.
    embedded_preprocessed: Vec<(Ident, LitStr)>,
    /// Per-proof field constants supplied to both the generated AIR and its
    /// interaction witness. These parameters are not committed columns.
    embedded_params: Vec<Ident>,
    /// Externally declared relations `relation name(arity);`, referenced by
    /// `emit`/`consume` in bodies. Each becomes a `relation!` type and an
    /// `AirFnRelations` field, so two function systems can share one
    /// relation by drawing it once and passing it in.
    relations: Vec<(Ident, usize)>,
    fns: Vec<AirFn>,
}

impl Parse for AirFnsInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let key: Ident = input.parse()?;
        if key != "max_degree" {
            return Err(syn::Error::new(key.span(), "expected `max_degree: N,`"));
        }
        input.parse::<Token![:]>()?;
        let lit: syn::LitInt = input.parse()?;
        let max_degree: usize = lit.base10_parse()?;
        if !(2..=3).contains(&max_degree) {
            // The component shells use max_constraint_log_degree_bound =
            // log_size + 1, which admits constraint degree 3.
            return Err(syn::Error::new(
                lit.span(),
                "max_degree must be 2 or 3 (the component degree bound admits 3)",
            ));
        }
        input.parse::<Token![,]>()?;

        let embedded = if input
            .cursor()
            .ident()
            .is_some_and(|(ident, _)| ident == "embedded")
        {
            input.parse::<Ident>()?;
            input.parse::<Token![:]>()?;
            let flags_content;
            bracketed!(flags_content in input);
            let flags: Punctuated<Ident, Token![,]> =
                flags_content.parse_terminated(Ident::parse, Token![,])?;
            input.parse::<Token![,]>()?;
            Some(flags.into_iter().collect())
        } else {
            None
        };

        let embedded_component = if input
            .cursor()
            .ident()
            .is_some_and(|(ident, _)| ident == "embedded_component")
        {
            input.parse::<Ident>()?;
            input.parse::<Token![:]>()?;
            let lit: syn::LitBool = input.parse()?;
            input.parse::<Token![,]>()?;
            lit.value
        } else {
            false
        };

        let embedded_enabler_boolean = if input
            .cursor()
            .ident()
            .is_some_and(|(ident, _)| ident == "embedded_enabler_boolean")
        {
            input.parse::<Ident>()?;
            input.parse::<Token![:]>()?;
            let lit: syn::LitBool = input.parse()?;
            input.parse::<Token![,]>()?;
            lit.value
        } else {
            true
        };

        let embedded_relations = if input
            .cursor()
            .ident()
            .is_some_and(|(ident, _)| ident == "embedded_relations")
        {
            input.parse::<Ident>()?;
            input.parse::<Token![:]>()?;
            let path = input.parse::<Path>()?;
            input.parse::<Token![,]>()?;
            path
        } else {
            syn::parse_quote!(crate::relations::Relations)
        };

        let logup_batch = if input
            .cursor()
            .ident()
            .is_some_and(|(ident, _)| ident == "logup_batch")
        {
            input.parse::<Ident>()?;
            input.parse::<Token![:]>()?;
            let lit = input.parse::<syn::LitInt>()?;
            input.parse::<Token![,]>()?;
            let batch = lit.base10_parse::<usize>()?;
            if !matches!(batch, 1 | 2) {
                return Err(syn::Error::new(
                    lit.span(),
                    "logup_batch must be 1 or 2 under the supported degree bound",
                ));
            }
            batch
        } else {
            1
        };

        let embedded_dynamic_component = if input
            .cursor()
            .ident()
            .is_some_and(|(ident, _)| ident == "embedded_dynamic_component")
        {
            input.parse::<Ident>()?;
            input.parse::<Token![:]>()?;
            let lit = input.parse::<syn::LitBool>()?;
            input.parse::<Token![,]>()?;
            lit.value
        } else {
            false
        };

        let embedded_preprocessed = if input
            .cursor()
            .ident()
            .is_some_and(|(ident, _)| ident == "embedded_preprocessed")
        {
            input.parse::<Ident>()?;
            input.parse::<Token![:]>()?;
            let columns_content;
            braced!(columns_content in input);
            let mut columns = Vec::new();
            while !columns_content.is_empty() {
                let name: Ident = columns_content.parse()?;
                columns_content.parse::<Token![:]>()?;
                let id: LitStr = columns_content.parse()?;
                columns.push((name, id));
                if columns_content.peek(Token![,]) {
                    columns_content.parse::<Token![,]>()?;
                }
            }
            input.parse::<Token![,]>()?;
            columns
        } else {
            Vec::new()
        };

        let embedded_params = if input
            .cursor()
            .ident()
            .is_some_and(|(ident, _)| ident == "embedded_params")
        {
            input.parse::<Ident>()?;
            input.parse::<Token![:]>()?;
            let params_content;
            bracketed!(params_content in input);
            let params: Punctuated<Ident, Token![,]> =
                params_content.parse_terminated(Ident::parse, Token![,])?;
            input.parse::<Token![,]>()?;
            params.into_iter().collect()
        } else {
            Vec::new()
        };

        // Externally declared relations: `relation name(arity);`.
        let mut relations = Vec::new();
        while input
            .cursor()
            .ident()
            .is_some_and(|(ident, _)| ident == "relation")
        {
            input.parse::<Ident>()?;
            let name: Ident = input.parse()?;
            let arity_content;
            parenthesized!(arity_content in input);
            let arity: syn::LitInt = arity_content.parse()?;
            input.parse::<Token![;]>()?;
            relations.push((name, arity.base10_parse()?));
        }

        let mut fns = Vec::new();
        while !input.is_empty() {
            fns.push(parse_fn(input)?);
        }
        Ok(AirFnsInput {
            max_degree,
            embedded,
            embedded_component,
            embedded_enabler_boolean,
            embedded_relations,
            logup_batch,
            embedded_dynamic_component,
            embedded_preprocessed,
            embedded_params,
            relations,
            fns,
        })
    }
}

fn parse_fn(input: ParseStream) -> syn::Result<AirFn> {
    let inline = input
        .cursor()
        .ident()
        .is_some_and(|(ident, _)| ident == "inline");
    if inline {
        input.parse::<Ident>()?;
    }
    input.parse::<Token![fn]>()?;
    let name: Ident = input.parse()?;
    let params_content;
    parenthesized!(params_content in input);
    let mut params = Vec::new();
    while !params_content.is_empty() {
        params.push(parse_param(&params_content)?);
        if params_content.peek(Token![,]) {
            params_content.parse::<Token![,]>()?;
        }
    }

    let body_content;
    braced!(body_content in input);
    let (body, rets) = parse_block(&body_content, true)?;
    let rets =
        rets.ok_or_else(|| syn::Error::new(name.span(), "function body must end with `return`"))?;
    Ok(AirFn {
        inline,
        name,
        params,
        body,
        rets,
    })
}

fn parse_param(input: ParseStream) -> syn::Result<Param> {
    let name: Ident = input.parse()?;
    let size = if input.peek(Token![:]) {
        input.parse::<Token![:]>()?;
        parse_param_type(input)?
    } else if input.peek(syn::token::Bracket) {
        let size_content;
        bracketed!(size_content in input);
        let lit: syn::LitInt = size_content.parse()?;
        Some(lit.base10_parse()?)
    } else {
        None
    };
    Ok(Param { name, size })
}

fn parse_param_type(input: ParseStream) -> syn::Result<Option<usize>> {
    if input.peek(syn::token::Bracket) {
        let array_content;
        bracketed!(array_content in input);
        parse_felt_keyword(&array_content)?;
        array_content.parse::<Token![;]>()?;
        let lit: syn::LitInt = array_content.parse()?;
        return Ok(Some(lit.base10_parse()?));
    }

    parse_felt_keyword(input)?;
    Ok(None)
}

fn parse_felt_keyword(input: ParseStream) -> syn::Result<()> {
    let keyword: Ident = input.parse()?;
    if keyword == "felt" {
        Ok(())
    } else {
        Err(syn::Error::new(
            keyword.span(),
            "expected `felt` or `[felt; N]`",
        ))
    }
}

/// Parse a statement block; `allow_return` only for the function's top
/// level (loops cannot return).
fn parse_block(
    input: ParseStream,
    allow_return: bool,
) -> syn::Result<(Vec<FnStmt>, Option<Vec<Expr>>)> {
    let mut body = Vec::new();
    let mut rets = None;
    while !input.is_empty() {
        if input.peek(Token![let]) {
            input.parse::<Token![let]>()?;
            let names: Vec<Ident> = if input.peek(syn::token::Paren) {
                let tuple;
                parenthesized!(tuple in input);
                let names: Punctuated<Ident, Token![,]> =
                    tuple.parse_terminated(Ident::parse, Token![,])?;
                names.into_iter().collect()
            } else {
                vec![input.parse()?]
            };
            input.parse::<Token![=]>()?;
            let value: Expr = input.parse()?;
            input.parse::<Token![;]>()?;
            body.push(FnStmt::Let { names, value });
        } else if input.peek(Token![for]) {
            input.parse::<Token![for]>()?;
            let var: Ident = input.parse()?;
            input.parse::<Token![in]>()?;
            let start: syn::LitInt = input.parse()?;
            input.parse::<Token![..]>()?;
            let end: syn::LitInt = input.parse()?;
            let loop_content;
            braced!(loop_content in input);
            let (loop_body, loop_rets) = parse_block(&loop_content, false)?;
            debug_assert!(loop_rets.is_none());
            body.push(FnStmt::For {
                var,
                start: start.base10_parse()?,
                end: end.base10_parse()?,
                body: loop_body,
            });
        } else if input.peek(Ident) && input.cursor().ident().is_some_and(|(i, _)| i == "assert") {
            input.parse::<Ident>()?;
            // `lhs == rhs` parses as one equality expression.
            let comparison: Expr = input.parse()?;
            input.parse::<Token![;]>()?;
            let Expr::Binary(binary) = comparison else {
                return Err(syn::Error::new_spanned(
                    comparison,
                    "assert takes `lhs == rhs`",
                ));
            };
            if !matches!(binary.op, syn::BinOp::Eq(_)) {
                return Err(syn::Error::new_spanned(binary, "assert takes `lhs == rhs`"));
            }
            body.push(FnStmt::Assert {
                lhs: *binary.left,
                rhs: *binary.right,
            });
        } else if input.peek(Ident) && input.cursor().ident().is_some_and(|(i, _)| i == "hint") {
            input.parse::<Ident>()?;
            let name: Ident = input.parse()?;
            input.parse::<Token![=]>()?;
            let expr: Expr = input.parse()?;
            input.parse::<Token![;]>()?;
            body.push(FnStmt::Hint { name, expr });
        } else if input.peek(Ident)
            && input
                .cursor()
                .ident()
                .is_some_and(|(i, _)| i == "constrain")
        {
            input.parse::<Ident>()?;
            let expr: Expr = input.parse()?;
            input.parse::<Token![;]>()?;
            body.push(FnStmt::Constrain { expr });
        } else if input.peek(Ident)
            && input
                .cursor()
                .ident()
                .is_some_and(|(i, _)| i == "emit" || i == "consume")
        {
            let keyword: Ident = input.parse()?;
            let emit = keyword == "emit";
            // Optional multiplicity: `emit(expr) r(args)` / `consume(expr) r(args)`.
            let mult = if input.peek(syn::token::Paren) {
                let mult_content;
                parenthesized!(mult_content in input);
                Some(mult_content.parse::<Expr>()?)
            } else {
                None
            };
            let relation: Ident = input.parse()?;
            let args_content;
            parenthesized!(args_content in input);
            let args: Punctuated<Expr, Token![,]> =
                args_content.parse_terminated(Expr::parse, Token![,])?;
            input.parse::<Token![;]>()?;
            body.push(FnStmt::Relation {
                relation,
                args: args.into_iter().collect(),
                emit,
                mult,
            });
        } else if allow_return && input.peek(Token![return]) {
            input.parse::<Token![return]>()?;
            let exprs: Vec<Expr> = if input.peek(syn::token::Paren) {
                let tuple;
                parenthesized!(tuple in input);
                let exprs: Punctuated<Expr, Token![,]> =
                    tuple.parse_terminated(Expr::parse, Token![,])?;
                exprs.into_iter().collect()
            } else {
                vec![input.parse()?]
            };
            input.parse::<Token![;]>()?;
            if !input.is_empty() {
                return Err(syn::Error::new(
                    input.span(),
                    "return must be the last statement",
                ));
            }
            rets = Some(exprs);
        } else {
            return Err(syn::Error::new(
                input.span(),
                "expected `let`, `assert`, `for`, `emit`, `consume`, or `return`",
            ));
        }
    }
    Ok((body, rets))
}

// =============================================================================
// Compile-time expression utilities
// =============================================================================

/// Substitute a loop variable with an integer literal, everywhere — index
/// positions and `constant(...)` arguments included.
fn substitute(expr: &Expr, var: &Ident, value: usize) -> Expr {
    struct Substituter<'a> {
        var: &'a Ident,
        value: usize,
    }
    impl syn::visit_mut::VisitMut for Substituter<'_> {
        fn visit_expr_mut(&mut self, expr: &mut Expr) {
            if let Expr::Path(path) = expr
                && path.path.is_ident(self.var)
            {
                let lit = syn::LitInt::new(&self.value.to_string(), self.var.span());
                *expr = syn::parse_quote!(#lit);
                return;
            }
            syn::visit_mut::visit_expr_mut(self, expr);
        }
    }
    let mut expr = expr.clone();
    syn::visit_mut::VisitMut::visit_expr_mut(&mut Substituter { var, value }, &mut expr);
    expr
}

fn substitute_stmt(stmt: &FnStmt, var: &Ident, value: usize) -> FnStmt {
    match stmt {
        FnStmt::Let { names, value: v } => FnStmt::Let {
            names: names.clone(),
            value: substitute(v, var, value),
        },
        FnStmt::Assert { lhs, rhs } => FnStmt::Assert {
            lhs: substitute(lhs, var, value),
            rhs: substitute(rhs, var, value),
        },
        FnStmt::For {
            var: inner,
            start,
            end,
            body,
        } => FnStmt::For {
            var: inner.clone(),
            start: *start,
            end: *end,
            body: body
                .iter()
                .map(|s| substitute_stmt(s, var, value))
                .collect(),
        },
        FnStmt::Relation {
            relation,
            args,
            emit,
            mult,
        } => FnStmt::Relation {
            relation: relation.clone(),
            args: args.iter().map(|a| substitute(a, var, value)).collect(),
            emit: *emit,
            mult: mult.as_ref().map(|m| substitute(m, var, value)),
        },
        FnStmt::Hint { name, expr } => FnStmt::Hint {
            name: name.clone(),
            expr: substitute(expr, var, value),
        },
        FnStmt::Constrain { expr } => FnStmt::Constrain {
            expr: substitute(expr, var, value),
        },
    }
}

/// Evaluate a compile-time index expression: integer arithmetic including
/// division and remainder (separate from the field-constant folder, where
/// `/` would be wrong).
fn index_eval(expr: &Expr) -> syn::Result<usize> {
    let err = || syn::Error::new_spanned(expr, "expected a constant index expression");
    match expr {
        Expr::Lit(lit) => match &lit.lit {
            syn::Lit::Int(int) => Ok(int.base10_parse()?),
            _ => Err(err()),
        },
        Expr::Binary(binary) => {
            let left = index_eval(&binary.left)?;
            let right = index_eval(&binary.right)?;
            match binary.op {
                syn::BinOp::Add(_) => Ok(left + right),
                syn::BinOp::Sub(_) => left.checked_sub(right).ok_or_else(err),
                syn::BinOp::Mul(_) => Ok(left * right),
                syn::BinOp::Div(_) => Ok(left / right),
                syn::BinOp::Rem(_) => Ok(left % right),
                _ => Err(err()),
            }
        }
        Expr::Paren(paren) => index_eval(&paren.expr),
        Expr::Group(group) => index_eval(&group.expr),
        _ => Err(err()),
    }
}

// =============================================================================
// Degree-budget lowering
// =============================================================================

/// A value in the frame: a committed column or an inline (derived)
/// expression of a known degree, referred to by its internal
/// (version-suffixed) cell name — or an array of values.
#[derive(Clone)]
enum Value {
    Scalar { cell: Ident, degree: usize },
    Array(Vec<Value>),
}

impl Value {
    fn scalar(&self) -> syn::Result<(&Ident, usize)> {
        match self {
            Value::Scalar { cell, degree } => Ok((cell, *degree)),
            Value::Array(_) => Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "expected a scalar, found an array",
            )),
        }
    }

    fn flatten(&self) -> Vec<(Ident, usize)> {
        match self {
            Value::Scalar { cell, degree } => vec![(cell.clone(), *degree)],
            Value::Array(elements) => elements.iter().flat_map(Value::flatten).collect(),
        }
    }
}

enum FillStep {
    /// `let cell = expr;` over BaseField values.
    Expr { cell: Ident, expr: Expr },
    /// `let [rets...] = call_callee(tables, [args...]);`
    Call {
        rets: Vec<Ident>,
        callee: Ident,
        args: Vec<Ident>,
    },
}

struct Lowerer<'a> {
    max_degree: usize,
    /// Internal cell names with their degrees; lowered expressions
    /// reference cells only.
    cells: HashMap<String, usize>,
    /// Used internal names, for fresh-name generation (shadowing).
    used: HashMap<String, usize>,
    /// Committed columns beyond the arguments, in creation order.
    extra_columns: Vec<Ident>,
    /// Inline (derived) cells: (name, lowered expr), in creation order.
    derived: Vec<(Ident, Expr)>,
    constraints: Vec<Expr>,
    /// Ungated constraints from `constrain` (added without the enabler gate).
    raw_constraints: Vec<Expr>,
    fill: Vec<FillStep>,
    /// Activations made: (callee, flattened arg cells, flattened ret cells).
    calls: Vec<(Ident, Vec<Ident>, Vec<Ident>)>,
    /// External relation contributions: (relation, arg cells, emit, mult cell;
    /// mult `None` means enabler).
    relation_entries: Vec<(Ident, Vec<Ident>, bool, Option<Ident>)>,
    /// Common-subexpression cache for materialized cells.
    cse: HashMap<String, Ident>,
    /// Flattened signatures of table-backed functions lowered so far.
    arities: &'a HashMap<String, (usize, usize)>,
    /// Arities of externally declared relations.
    relation_arities: &'a HashMap<String, usize>,
    inline_fns: &'a HashMap<String, AirFn>,
    fn_name: Ident,
}

impl Lowerer<'_> {
    fn fresh(&mut self, base: &Ident) -> Ident {
        let key = base.to_string();
        let count = self.used.entry(key).or_insert(0);
        *count += 1;
        if *count == 1 {
            base.clone()
        } else {
            format_ident!("{}_v{}", base, *count)
        }
    }

    fn register_column(&mut self, base: &Ident) -> Ident {
        let cell = self.fresh(base);
        self.cells.insert(cell.to_string(), 1);
        cell
    }

    /// Register an inline derived cell holding a lowered expression.
    fn register_derived(&mut self, base: &Ident, expr: Expr, degree: usize) -> Ident {
        let cell = self.fresh(base);
        self.cells.insert(cell.to_string(), degree);
        self.derived.push((cell.clone(), expr.clone()));
        self.fill.push(FillStep::Expr {
            cell: cell.clone(),
            expr,
        });
        cell
    }

    /// Materialize a lowered expression as a committed column (CSE-cached):
    /// an equality constraint pins it, and its degree drops to 1.
    fn materialize(&mut self, expr: Expr) -> Expr {
        let key = expr.to_token_stream().to_string();
        if let Some(cell) = self.cse.get(&key) {
            let cell = cell.clone();
            return syn::parse_quote!(#cell);
        }
        let base = format_ident!("{}_t{}", self.fn_name, self.cse.len());
        let cell = self.register_column(&base);
        self.extra_columns.push(cell.clone());
        self.constraints.push(syn::parse_quote!(#cell - (#expr)));
        self.fill.push(FillStep::Expr {
            cell: cell.clone(),
            expr: expr.clone(),
        });
        self.cse.insert(key, cell.clone());
        syn::parse_quote!(#cell)
    }

    fn lower_product<S: ToTokens + ?Sized>(
        &mut self,
        mut left: Expr,
        mut dl: usize,
        mut right: Expr,
        mut dr: usize,
        budget: usize,
        span: &S,
    ) -> syn::Result<(Expr, usize)> {
        if matches!(const_eval(&left), Ok(1)) {
            return Ok((right, dr));
        }
        if matches!(const_eval(&right), Ok(1)) {
            return Ok((left, dl));
        }

        // Unroll the product until it fits: materialize the higher-degree
        // side (additions never trigger this).
        while dl + dr > budget {
            if dl >= dr && dl > 1 {
                left = self.materialize(left);
                dl = 1;
            } else if dr > 1 {
                right = self.materialize(right);
                dr = 1;
            } else {
                return Err(syn::Error::new_spanned(
                    span,
                    format!("cannot reduce product below degree {}", dl + dr),
                ));
            }
        }
        Ok((syn::parse_quote!((#left * #right)), dl + dr))
    }

    fn lower_pow<S: ToTokens + ?Sized>(
        &mut self,
        base: &Expr,
        exponent: usize,
        scope: &HashMap<String, Value>,
        budget: usize,
        span: &S,
    ) -> syn::Result<(Expr, usize)> {
        if exponent == 0 {
            return Ok((syn::parse_quote!(1), 0));
        }

        let (mut power, mut power_degree) = self.lower(base, scope, budget)?;
        let mut result: Option<(Expr, usize)> = None;
        let mut remaining = exponent;
        while remaining > 0 {
            if remaining & 1 == 1 {
                result = Some(match result {
                    None => (power.clone(), power_degree),
                    Some((acc, acc_degree)) => self.lower_product(
                        acc,
                        acc_degree,
                        power.clone(),
                        power_degree,
                        budget,
                        span,
                    )?,
                });
            }

            remaining >>= 1;
            if remaining > 0 {
                let squared = self.lower_product(
                    power.clone(),
                    power_degree,
                    power.clone(),
                    power_degree,
                    budget,
                    span,
                )?;
                power = squared.0;
                power_degree = squared.1;
            }
        }

        match result {
            Some(value) => Ok(value),
            None => Ok((syn::parse_quote!(1), 0)),
        }
    }

    /// Lower a scalar expression over a user-name scope so its degree fits
    /// `budget`, materializing multiplicative subtrees as needed. Returns
    /// the cell-level expression and its degree.
    fn lower(
        &mut self,
        expr: &Expr,
        scope: &HashMap<String, Value>,
        budget: usize,
    ) -> syn::Result<(Expr, usize)> {
        // Constant subtrees have degree 0 and stay verbatim (the backend
        // folds them at expansion time).
        if const_eval(expr).is_ok() {
            return Ok((expr.clone(), 0));
        }
        match expr {
            Expr::Path(path) => {
                let ident = path.path.get_ident().ok_or_else(|| {
                    syn::Error::new_spanned(path, "only plain names are usable in expressions")
                })?;
                let value = scope.get(&ident.to_string()).ok_or_else(|| {
                    syn::Error::new_spanned(
                        ident,
                        format!("`{ident}` is not defined in this frame"),
                    )
                })?;
                let (cell, degree) = value.scalar()?;
                Ok((syn::parse_quote!(#cell), degree))
            }
            Expr::Index(index) => {
                let Expr::Path(path) = index.expr.as_ref() else {
                    return Err(syn::Error::new_spanned(index, "only named arrays index"));
                };
                let ident = path.path.require_ident()?;
                let Some(Value::Array(elements)) = scope.get(&ident.to_string()) else {
                    return Err(syn::Error::new_spanned(
                        ident,
                        format!("`{ident}` is not an array in this frame"),
                    ));
                };
                let position = index_eval(&index.index)?;
                let element = elements.get(position).ok_or_else(|| {
                    syn::Error::new_spanned(
                        index,
                        format!("index {position} out of bounds for `{ident}`"),
                    )
                })?;
                let (cell, degree) = element.scalar()?;
                Ok((syn::parse_quote!(#cell), degree))
            }
            Expr::Call(call) => {
                if let Expr::Path(func) = call.func.as_ref()
                    && func.path.is_ident("constant")
                {
                    return Ok((expr.clone(), 0));
                }
                if let Expr::Path(func) = call.func.as_ref()
                    && func.path.is_ident("inv")
                    && call.args.len() == 1
                {
                    // inv(c): multiplicative inverse of a constant, folded to
                    // a field-constant literal at expansion (Fermat). Degree 0.
                    let value = crate::trace_tables::const_eval(&call.args[0])?;
                    if value == 0 {
                        return Err(syn::Error::new_spanned(call, "cannot invert zero"));
                    }
                    let inverse =
                        crate::trace_tables::m31_pow(value, crate::trace_tables::M31_PRIME - 2)
                            as u32;
                    return Ok((syn::parse_quote!(#inverse), 0));
                }
                if let Expr::Path(func) = call.func.as_ref()
                    && func.path.is_ident("sum")
                    && call.args.len() == 3
                {
                    // sum(j, a..b, body): an additive fold, lowered inline.
                    let var = expect_ident(&call.args[0])?;
                    let (start, end) = expect_range(&call.args[1])?;
                    let mut total: Option<(Expr, usize)> = None;
                    for value in start..end {
                        let body = substitute(&call.args[2], &var, value);
                        let (lowered, degree) = self.lower(&body, scope, budget)?;
                        total = Some(match total {
                            None => (lowered, degree),
                            Some((acc, acc_degree)) => {
                                (syn::parse_quote!((#acc + #lowered)), acc_degree.max(degree))
                            }
                        });
                    }
                    return total
                        .ok_or_else(|| syn::Error::new_spanned(call, "sum over an empty range"));
                }
                Err(syn::Error::new_spanned(
                    call,
                    "function calls must be bound directly: `let r = callee(...);`",
                ))
            }
            Expr::Binary(binary) => match binary.op {
                syn::BinOp::Add(_) | syn::BinOp::Sub(_) => {
                    let (left, dl) = self.lower(&binary.left, scope, budget)?;
                    let (right, dr) = self.lower(&binary.right, scope, budget)?;
                    let op = &binary.op;
                    Ok((syn::parse_quote!((#left #op #right)), dl.max(dr)))
                }
                syn::BinOp::Mul(_) => {
                    if let Expr::Unary(unary) = binary.right.as_ref()
                        && matches!(unary.op, syn::UnOp::Deref(_))
                    {
                        let exponent = index_eval(&unary.expr)?;
                        return self.lower_pow(&binary.left, exponent, scope, budget, binary);
                    }

                    let (left, dl) = self.lower(&binary.left, scope, budget)?;
                    let (right, dr) = self.lower(&binary.right, scope, budget)?;
                    self.lower_product(left, dl, right, dr, budget, binary)
                }
                _ => Err(syn::Error::new_spanned(
                    binary,
                    "only +, -, *, and ** const are supported",
                )),
            },
            Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_)) => {
                let (inner, degree) = self.lower(&unary.expr, scope, budget)?;
                Ok((syn::parse_quote!((-#inner)), degree))
            }
            Expr::Paren(paren) => self.lower(&paren.expr, scope, budget),
            Expr::Group(group) => self.lower(&group.expr, scope, budget),
            other => Err(syn::Error::new_spanned(
                other,
                "unsupported expression in a felt function",
            )),
        }
    }

    /// Lower a `let` right-hand side into frame values (scalar, array, or
    /// call results).
    fn lower_value(
        &mut self,
        names: &[Ident],
        value: &Expr,
        scope: &HashMap<String, Value>,
        budget: usize,
    ) -> syn::Result<Vec<Value>> {
        // Array literal: one derived per element.
        if let Expr::Array(array) = value {
            let elements = array
                .elems
                .iter()
                .enumerate()
                .map(|(position, element)| {
                    let (lowered, degree) = self.lower(element, scope, budget)?;
                    let base = format_ident!("{}_{}", &names[0], position);
                    let cell = self.register_derived(&base, lowered, degree);
                    Ok(Value::Scalar { cell, degree })
                })
                .collect::<syn::Result<Vec<_>>>()?;
            return Ok(vec![Value::Array(elements)]);
        }
        if let Expr::Call(call) = value
            && let Expr::Path(func) = call.func.as_ref()
            && let Some(callee) = func.path.get_ident()
        {
            match callee.to_string().as_str() {
                // map(j, a..b, body): an array built per element.
                "map" if call.args.len() == 3 => {
                    let var = expect_ident(&call.args[0])?;
                    let (start, end) = expect_range(&call.args[1])?;
                    let elements = (start..end)
                        .map(|position| {
                            let body = substitute(&call.args[2], &var, position);
                            let (lowered, degree) = self.lower(&body, scope, budget)?;
                            let base = format_ident!("{}_{}", &names[0], position);
                            let cell = self.register_derived(&base, lowered, degree);
                            Ok(Value::Scalar { cell, degree })
                        })
                        .collect::<syn::Result<Vec<_>>>()?;
                    return Ok(vec![Value::Array(elements)]);
                }
                // update(arr, index, expr): a copy with one element replaced.
                "update" if call.args.len() == 3 => {
                    let array = expect_ident(&call.args[0])?;
                    let Some(Value::Array(elements)) = scope.get(&array.to_string()) else {
                        return Err(syn::Error::new_spanned(
                            &call.args[0],
                            "update takes an array name",
                        ));
                    };
                    let mut elements = elements.clone();
                    let position = index_eval(&call.args[1])?;
                    if position >= elements.len() {
                        return Err(syn::Error::new_spanned(
                            &call.args[1],
                            "update index out of bounds",
                        ));
                    }
                    let (lowered, degree) = self.lower(&call.args[2], scope, budget)?;
                    let base = format_ident!("{}_{}", &names[0], position);
                    let cell = self.register_derived(&base, lowered, degree);
                    elements[position] = Value::Scalar { cell, degree };
                    return Ok(vec![Value::Array(elements)]);
                }
                "constant" | "sum" | "pow2" | "inv" => {}
                _ => {
                    // A sibling-function call: inline splice or activation.
                    let args = call.args.iter().cloned().collect::<Vec<_>>();
                    return self.lower_call(names, callee, &args, scope, budget);
                }
            }
        }
        // Scalar expression.
        if names.len() != 1 {
            return Err(syn::Error::new_spanned(
                value,
                "tuple bindings are only for function calls",
            ));
        }
        let (lowered, degree) = self.lower(value, scope, budget)?;
        let cell = self.register_derived(&names[0], lowered, degree);
        Ok(vec![Value::Scalar { cell, degree }])
    }

    /// Lower a call: splice an `inline fn` into this frame, or record an
    /// activation of a table-backed function.
    fn lower_call(
        &mut self,
        names: &[Ident],
        callee: &Ident,
        args: &[Expr],
        scope: &HashMap<String, Value>,
        budget: usize,
    ) -> syn::Result<Vec<Value>> {
        if let Some(inline_fn) = self.inline_fns.get(&callee.to_string()) {
            // Bind arguments into a fresh local scope, then process the body
            // statements in this same frame (shared columns, CSE, fill).
            if args.len() != inline_fn.params.len() {
                return Err(syn::Error::new_spanned(
                    callee,
                    format!("`{callee}` takes {} arguments", inline_fn.params.len()),
                ));
            }
            let mut local: HashMap<String, Value> = HashMap::new();
            for (param, arg) in inline_fn.params.iter().zip(args) {
                let value = match param.size {
                    None => {
                        let (lowered, degree) = self.lower(arg, scope, budget)?;
                        let base = format_ident!("{}_{}", callee, param.name);
                        let cell = self.register_derived(&base, lowered, degree);
                        Value::Scalar { cell, degree }
                    }
                    Some(size) => {
                        // Array arguments pass by name.
                        let ident = expect_ident(arg)?;
                        let Some(value @ Value::Array(elements)) = scope.get(&ident.to_string())
                        else {
                            return Err(syn::Error::new_spanned(
                                arg,
                                "array arguments pass an array name",
                            ));
                        };
                        if elements.len() != size {
                            return Err(syn::Error::new_spanned(
                                arg,
                                format!(
                                    "`{ident}` has {} elements, expected {size}",
                                    elements.len()
                                ),
                            ));
                        }
                        value.clone()
                    }
                };
                local.insert(param.name.to_string(), value);
            }
            let body = clone_body(&inline_fn.body);
            let rets = inline_fn.rets.clone();
            self.lower_block(&body, &mut local, budget)?;
            let rets = rets
                .iter()
                .map(|ret| self.lower_ret(ret, &local, budget))
                .collect::<syn::Result<Vec<_>>>()?;
            return bind_rets(names, rets, value_error(callee));
        }

        // An activation: flattened arguments and returned cells through the
        // callee's io relation.
        let Some(&(n_args, n_rets)) = self.arities.get(&callee.to_string()) else {
            return Err(syn::Error::new_spanned(
                callee,
                format!("unknown function `{callee}` (calls reference earlier definitions)"),
            ));
        };
        let mut arg_cells = Vec::new();
        for arg in args {
            // Arrays flatten; scalars lower into derived cells so the io
            // tuple references cells only.
            if let Ok(ident) = expect_ident(arg)
                && let Some(value @ Value::Array(_)) = scope.get(&ident.to_string())
            {
                for (cell, _) in value.flatten() {
                    arg_cells.push(cell);
                }
                continue;
            }
            let (lowered, degree) = self.lower(arg, scope, budget)?;
            let base = format_ident!("{}_a{}", callee, arg_cells.len());
            arg_cells.push(self.register_derived(&base, lowered, degree));
        }
        if arg_cells.len() != n_args {
            return Err(syn::Error::new_spanned(
                callee,
                format!("`{callee}` takes {n_args} felts, got {}", arg_cells.len()),
            ));
        }
        // Returned values are witness columns received through the relation.
        let mut ret_cells = Vec::new();
        let mut rets = Vec::new();
        if names.len() == 1 && n_rets > 1 {
            // Single binder for a multi-return callee: an array.
            let elements = (0..n_rets)
                .map(|position| {
                    let base = format_ident!("{}_{}", &names[0], position);
                    let cell = self.register_column(&base);
                    self.extra_columns.push(cell.clone());
                    ret_cells.push(cell.clone());
                    Value::Scalar { cell, degree: 1 }
                })
                .collect();
            rets.push(Value::Array(elements));
        } else {
            if names.len() != n_rets {
                return Err(syn::Error::new_spanned(
                    callee,
                    format!("`{callee}` returns {n_rets} values"),
                ));
            }
            for name in names {
                let cell = self.register_column(name);
                self.extra_columns.push(cell.clone());
                ret_cells.push(cell.clone());
                rets.push(Value::Scalar { cell, degree: 1 });
            }
        }
        self.fill.push(FillStep::Call {
            rets: ret_cells.clone(),
            callee: callee.clone(),
            args: arg_cells.clone(),
        });
        self.calls.push((callee.clone(), arg_cells, ret_cells));
        Ok(rets)
    }

    fn lower_block(
        &mut self,
        body: &[FnStmt],
        scope: &mut HashMap<String, Value>,
        budget: usize,
    ) -> syn::Result<()> {
        for stmt in body {
            match stmt {
                FnStmt::Let { names, value } => {
                    let values = self.lower_value(names, value, scope, budget)?;
                    if values.len() == 1 {
                        scope.insert(
                            names[0].to_string(),
                            values.into_iter().next().expect("one value"),
                        );
                    } else {
                        for (name, value) in names.iter().zip(values) {
                            scope.insert(name.to_string(), value);
                        }
                    }
                }
                FnStmt::Assert { lhs, rhs } => {
                    // The enabler gate on emitted constraints costs one
                    // degree: asserts share the cell budget.
                    let difference: Expr = syn::parse_quote!((#lhs) - (#rhs));
                    let (lowered, _) = self.lower(&difference, scope, self.max_degree - 1)?;
                    self.constraints.push(lowered);
                }
                FnStmt::For {
                    var,
                    start,
                    end,
                    body,
                } => {
                    for value in *start..*end {
                        let unrolled: Vec<FnStmt> = body
                            .iter()
                            .map(|s| substitute_stmt(s, var, value))
                            .collect();
                        self.lower_block(&unrolled, scope, budget)?;
                    }
                }
                FnStmt::Relation {
                    relation,
                    args,
                    emit,
                    mult,
                } => {
                    let Some(&arity) = self.relation_arities.get(&relation.to_string()) else {
                        return Err(syn::Error::new_spanned(
                            relation,
                            format!(
                                "unknown relation `{relation}` (declare it with `relation {relation}(arity);`)"
                            ),
                        ));
                    };
                    // Lower an expression to a cell, reusing a bare column/cell
                    // directly (only compound expressions get a fresh cell).
                    let to_cell =
                        |lowerer: &mut Self, expr: &Expr, base: Ident| -> syn::Result<Ident> {
                            let (lowered, degree) = lowerer.lower(expr, scope, budget)?;
                            if let Expr::Path(path) = &lowered
                                && let Some(ident) = path.path.get_ident()
                            {
                                return Ok(ident.clone());
                            }
                            Ok(lowerer.register_derived(&base, lowered, degree))
                        };

                    // Optional multiplicity (default: enabler).
                    let mult_cell = match mult {
                        None => None,
                        Some(expr) => {
                            let base =
                                format_ident!("{}_mult{}", relation, self.relation_entries.len());
                            Some(to_cell(self, expr, base)?)
                        }
                    };

                    // Mirror activation-argument lowering: arrays flatten,
                    // scalars lower into cells so the tuple references cells.
                    let mut arg_cells = Vec::new();
                    for arg in args {
                        if let Ok(ident) = expect_ident(arg)
                            && let Some(value @ Value::Array(_)) = scope.get(&ident.to_string())
                        {
                            for (cell, _) in value.flatten() {
                                arg_cells.push(cell);
                            }
                            continue;
                        }
                        let base = format_ident!("{}_e{}", relation, self.relation_entries.len());
                        arg_cells.push(to_cell(self, arg, base)?);
                    }
                    if arg_cells.len() != arity {
                        return Err(syn::Error::new_spanned(
                            relation,
                            format!(
                                "`{relation}` has arity {arity}, got {} felts",
                                arg_cells.len()
                            ),
                        ));
                    }
                    self.relation_entries
                        .push((relation.clone(), arg_cells, *emit, mult_cell));
                }
                FnStmt::Hint { name, expr } => {
                    // A committed column (free in the AIR), filled by
                    // evaluating `expr` concretely. The body constrains it.
                    let (lowered, _) = self.lower(expr, scope, budget)?;
                    let cell = self.register_column(name);
                    self.extra_columns.push(cell.clone());
                    self.fill.push(FillStep::Expr {
                        cell: cell.clone(),
                        expr: lowered,
                    });
                    scope.insert(name.to_string(), Value::Scalar { cell, degree: 1 });
                }
                FnStmt::Constrain { expr } => {
                    // Ungated: the full degree budget is available (no enabler
                    // factor). The constraint must vanish on padding by its
                    // own structure (e.g. an opcode-flag factor).
                    let (lowered, _) = self.lower(expr, scope, self.max_degree)?;
                    self.raw_constraints.push(lowered);
                }
            }
        }
        Ok(())
    }

    /// Lower a return expression: a scalar, or an array name (flattened by
    /// the caller).
    fn lower_ret(
        &mut self,
        ret: &Expr,
        scope: &HashMap<String, Value>,
        budget: usize,
    ) -> syn::Result<Value> {
        if let Ok(ident) = expect_ident(ret)
            && let Some(value @ Value::Array(_)) = scope.get(&ident.to_string())
        {
            return Ok(value.clone());
        }
        let (lowered, degree) = self.lower(ret, scope, budget)?;
        let base = format_ident!("{}_ret", self.fn_name);
        let cell = self.register_derived(&base, lowered, degree);
        Ok(Value::Scalar { cell, degree })
    }
}

fn expect_ident(expr: &Expr) -> syn::Result<Ident> {
    if let Expr::Path(path) = expr
        && let Some(ident) = path.path.get_ident()
    {
        return Ok(ident.clone());
    }
    Err(syn::Error::new_spanned(expr, "expected a plain name"))
}

fn expect_range(expr: &Expr) -> syn::Result<(usize, usize)> {
    if let Expr::Range(range) = expr
        && let (Some(start), Some(end)) = (&range.start, &range.end)
        && matches!(range.limits, syn::RangeLimits::HalfOpen(_))
    {
        return Ok((index_eval(start)?, index_eval(end)?));
    }
    Err(syn::Error::new_spanned(
        expr,
        "expected a constant `a..b` range",
    ))
}

fn value_error(callee: &Ident) -> syn::Error {
    syn::Error::new_spanned(callee, "binder count does not match returned values")
}

fn bind_rets(names: &[Ident], rets: Vec<Value>, error: syn::Error) -> syn::Result<Vec<Value>> {
    // One binder taking everything (a single value or a flattened array of
    // scalars), or one binder per returned value.
    if names.len() == 1 {
        if rets.len() == 1 {
            return Ok(rets);
        }
        let flattened: Vec<Value> = rets
            .iter()
            .flat_map(Value::flatten)
            .map(|(cell, degree)| Value::Scalar { cell, degree })
            .collect();
        return Ok(vec![Value::Array(flattened)]);
    }
    if names.len() == rets.len() {
        return Ok(rets);
    }
    Err(error)
}

fn clone_body(body: &[FnStmt]) -> Vec<FnStmt> {
    body.iter()
        .map(|stmt| match stmt {
            FnStmt::Let { names, value } => FnStmt::Let {
                names: names.clone(),
                value: value.clone(),
            },
            FnStmt::Assert { lhs, rhs } => FnStmt::Assert {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            FnStmt::For {
                var,
                start,
                end,
                body,
            } => FnStmt::For {
                var: var.clone(),
                start: *start,
                end: *end,
                body: clone_body(body),
            },
            FnStmt::Relation {
                relation,
                args,
                emit,
                mult,
            } => FnStmt::Relation {
                relation: relation.clone(),
                args: args.clone(),
                emit: *emit,
                mult: mult.clone(),
            },
            FnStmt::Hint { name, expr } => FnStmt::Hint {
                name: name.clone(),
                expr: expr.clone(),
            },
            FnStmt::Constrain { expr } => FnStmt::Constrain { expr: expr.clone() },
        })
        .collect()
}

/// A lowered table-backed function, ready for backend generation.
struct LoweredFn {
    name: Ident,
    n_args: usize,
    n_rets: usize,
    /// Bare column layout (no derived/constraints/lookups — the felt
    /// front end generates a straight-line `evaluation()` instead, so deep
    /// cell DAGs evaluate once into locals rather than through recursive
    /// method calls).
    table: OpcodeDef,
    /// Derived cells in creation order: (cell, lowered expr).
    derived: Vec<(Ident, Expr)>,
    /// Materialization equalities and asserts, over cells.
    constraints: Vec<Expr>,
    /// Ungated `constrain` constraints (no enabler gate).
    raw_constraints: Vec<Expr>,
    /// Activations made: (callee, arg cells, ret cells).
    calls: Vec<(Ident, Vec<Ident>, Vec<Ident>)>,
    /// External relation contributions: (relation, arg cells, emit, mult cell).
    relation_entries: Vec<(Ident, Vec<Ident>, bool, Option<Ident>)>,
    fill: Vec<FillStep>,
    ret_cells: Vec<Ident>,
}

fn lower_fn(
    function: &AirFn,
    max_degree: usize,
    arities: &HashMap<String, (usize, usize)>,
    relation_arities: &HashMap<String, usize>,
    inline_fns: &HashMap<String, AirFn>,
    materialize_rets: bool,
    fixed_params: &std::collections::HashSet<String>,
) -> syn::Result<LoweredFn> {
    // Lookup-tuple elements appear in LogUp denominators whose singleton
    // constraint multiplies by one cumsum mask: budget max_degree - 1.
    let io_budget = max_degree - 1;
    let mut lowerer = Lowerer {
        max_degree,
        cells: HashMap::new(),
        used: HashMap::new(),
        extra_columns: Vec::new(),
        derived: Vec::new(),
        constraints: Vec::new(),
        raw_constraints: Vec::new(),
        fill: Vec::new(),
        calls: Vec::new(),
        relation_entries: Vec::new(),
        cse: HashMap::new(),
        arities,
        relation_arities,
        inline_fns,
        fn_name: function.name.clone(),
    };

    // Every table has one generated activity column. Making it a built-in
    // frame value lets a function gate optional relation multiplicities and
    // constrain auxiliary flags to real rows without duplicating that column
    // in its parameter list.
    let mut scope: HashMap<String, Value> = HashMap::new();
    let enabler = format_ident!("enabler");
    scope.insert(
        enabler.to_string(),
        Value::Scalar {
            cell: enabler,
            degree: 1,
        },
    );

    // Parameters are committed columns: scalars directly, arrays flattened
    // as `name_k`.
    let mut arg_columns: Vec<Ident> = Vec::new();
    for param in &function.params {
        if param.name == "enabler" {
            return Err(syn::Error::new(
                param.name.span(),
                "`enabler` is a built-in row-activity value",
            ));
        }
        let value = match param.size {
            None => {
                let cell = lowerer.register_column(&param.name);
                arg_columns.push(cell.clone());
                let degree = usize::from(!fixed_params.contains(&param.name.to_string()));
                Value::Scalar { cell, degree }
            }
            Some(size) => {
                let elements = (0..size)
                    .map(|position| {
                        let base = format_ident!("{}_{}", param.name, position);
                        let cell = lowerer.register_column(&base);
                        arg_columns.push(cell.clone());
                        Value::Scalar { cell, degree: 1 }
                    })
                    .collect();
                Value::Array(elements)
            }
        };
        scope.insert(param.name.to_string(), value);
    }

    lowerer.lower_block(&function.body, &mut scope, io_budget)?;

    let mut ret_cells: Vec<Ident> = Vec::new();
    for ret in &function.rets {
        let value = lowerer.lower_ret(ret, &scope, io_budget)?;
        for (cell, degree) in value.flatten() {
            // Embedded hosts pair activation entries, so the tuple must be
            // degree 1: commit every returned cell.
            if materialize_rets && degree > 1 {
                let expr: Expr = syn::parse_quote!(#cell);
                let Expr::Path(materialized) = lowerer.materialize(expr) else {
                    unreachable!("materialize returns a cell path");
                };
                ret_cells.push(materialized.path.require_ident()?.clone());
            } else {
                ret_cells.push(cell);
            }
        }
    }

    // Assemble the backend table: arguments, then call returns and
    // materialized intermediates in creation order (enabler is prepended by
    // the backend).
    let mut fields = arg_columns.clone();
    fields.extend(lowerer.extra_columns.clone());

    let table = OpcodeDef {
        name: function.name.clone(),
        fields,
        derived: Vec::new(),
        constraints: Vec::new(),
        lookups: LookupsDef {
            batch: 1,
            entries: Vec::new(),
        },
        air_only: false,
    };

    Ok(LoweredFn {
        name: function.name.clone(),
        n_args: arg_columns.len(),
        n_rets: ret_cells.len(),
        table,
        derived: lowerer.derived,
        constraints: lowerer.constraints,
        raw_constraints: lowerer.raw_constraints,
        calls: lowerer.calls,
        relation_entries: lowerer.relation_entries,
        fill: lowerer.fill,
        ret_cells,
    })
}

// =============================================================================
// Code generation
// =============================================================================

/// Rewrite a lowered cell expression into concrete `BaseField` arithmetic
/// for the witness fill (cells are local variables; constants fold).
fn concrete_expr(expr: &Expr) -> syn::Result<TokenStream2> {
    if let Ok(value) = const_eval(expr) {
        let value = value as u32;
        return Ok(quote! {
            stwo::core::fields::m31::BaseField::from_u32_unchecked(#value)
        });
    }
    match expr {
        Expr::Path(path) => Ok(quote!(#path)),
        Expr::Lit(lit) => {
            if let syn::Lit::Int(int) = &lit.lit {
                let value = int.base10_parse::<u32>()?;
                Ok(quote! {
                    stwo::core::fields::m31::BaseField::from_u32_unchecked(#value)
                })
            } else {
                Err(syn::Error::new_spanned(lit, "only integer literals"))
            }
        }
        Expr::Call(call) => {
            // constant(expr): verbatim u32 const from the invocation site.
            if let Expr::Path(func) = call.func.as_ref()
                && func.path.is_ident("constant")
                && call.args.len() == 1
            {
                let arg = &call.args[0];
                return Ok(quote! {
                    stwo::core::fields::m31::BaseField::from_u32_unchecked(#arg)
                });
            }
            Err(syn::Error::new_spanned(call, "unsupported call"))
        }
        Expr::Binary(binary) => {
            let left = concrete_expr(&binary.left)?;
            let right = concrete_expr(&binary.right)?;
            let op = &binary.op;
            Ok(quote!((#left #op #right)))
        }
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_)) => {
            let inner = concrete_expr(&unary.expr)?;
            Ok(quote!((-#inner)))
        }
        Expr::Paren(paren) => concrete_expr(&paren.expr),
        Expr::Group(group) => concrete_expr(&group.expr),
        other => Err(syn::Error::new_spanned(other, "unsupported expression")),
    }
}

/// Rewrite a lowered cell expression for the generic `evaluation()` body:
/// columns become `self.field.clone()`, derived cells become heap-vector
/// reads `cells[i].clone()` (the frame stays small however deep the
/// program is), constant subtrees fold into a single field constant.
fn air_expr(
    expr: &Expr,
    columns: &std::collections::HashSet<String>,
    cells: &HashMap<String, usize>,
) -> syn::Result<TokenStream2> {
    if let Ok(value) = const_eval(expr) {
        let value = value as u32;
        return Ok(quote! {
            T::from(stwo::core::fields::m31::BaseField::from_u32_unchecked(#value))
        });
    }
    match expr {
        Expr::Path(path) => {
            let ident = path.path.require_ident()?;
            if columns.contains(&ident.to_string()) {
                Ok(quote!(self.#ident.clone()))
            } else {
                let index = cells.get(&ident.to_string()).ok_or_else(|| {
                    syn::Error::new_spanned(ident, format!("unknown cell `{ident}`"))
                })?;
                Ok(quote!(cells[#index].clone()))
            }
        }
        Expr::Call(call) => {
            if let Expr::Path(func) = call.func.as_ref()
                && func.path.is_ident("constant")
                && call.args.len() == 1
            {
                let arg = &call.args[0];
                return Ok(quote! {
                    T::from(stwo::core::fields::m31::BaseField::from_u32_unchecked(#arg))
                });
            }
            Err(syn::Error::new_spanned(call, "unsupported call"))
        }
        Expr::Binary(binary) => {
            let left = air_expr(&binary.left, columns, cells)?;
            let right = air_expr(&binary.right, columns, cells)?;
            let op = &binary.op;
            Ok(quote!((#left #op #right)))
        }
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_)) => {
            let inner = air_expr(&unary.expr, columns, cells)?;
            Ok(quote!((-#inner)))
        }
        Expr::Paren(paren) => air_expr(&paren.expr, columns, cells),
        Expr::Group(group) => air_expr(&group.expr, columns, cells),
        other => Err(syn::Error::new_spanned(other, "unsupported expression")),
    }
}

/// Generate the straight-line `evaluation()` on the columns struct: every
/// derived cell computed once into a heap vector in dependency order (a
/// DAG, not an exponential tree — and no stack frame proportional to the
/// program depth, which would overflow default test-thread stacks in
/// debug builds), then the constraints and lookup entries over them.
fn generate_evaluation_impl(function: &LoweredFn) -> syn::Result<TokenStream2> {
    let columns_type = column_struct_name(&function.name);
    let columns: std::collections::HashSet<String> = std::iter::once("enabler".to_string())
        .chain(function.table.fields.iter().map(|f| f.to_string()))
        .collect();

    // Flag tables (opcode_*_flag columns) have no `enabler` column — the
    // shared column generator synthesizes `enabler()` as the flag sum, so the
    // row-activity indicator is sound by construction. Non-flag tables use the
    // committed `enabler` column.
    let enabler = if count_opcode_flags(&function.table.fields) == 0 {
        quote! { self.enabler.clone() }
    } else {
        quote! { self.enabler() }
    };

    let mut cell_indices: HashMap<String, usize> = HashMap::new();
    let mut cell_pushes: Vec<TokenStream2> = Vec::new();
    for (cell, expr) in &function.derived {
        let value = air_expr(expr, &columns, &cell_indices)?;
        cell_indices.insert(cell.to_string(), cell_pushes.len());
        cell_pushes.push(quote! { cells.push(#value); });
    }
    let n_cells = cell_pushes.len();

    // Unoptimized builds give every temporary in a function body its own
    // stack slot, so a single straight-line body over hundreds of cells
    // builds a multi-megabyte frame that overflows default test-thread
    // stacks. Splitting the pushes into small helper methods keeps each
    // frame bounded (debug builds never inline, so frames pop between
    // chunks); optimized builds inline them back into one body.
    const CHUNK: usize = 32;
    let cell_chunk_fns: Vec<TokenStream2> = cell_pushes
        .chunks(CHUNK)
        .enumerate()
        .map(|(i, chunk)| {
            let name = format_ident!("__evaluation_cells_{i}");
            quote! {
                #[doc(hidden)]
                fn #name(&self, cells: &mut Vec<T>) {
                    #(#chunk)*
                }
            }
        })
        .collect();
    let cell_chunk_calls: Vec<TokenStream2> = (0..cell_chunk_fns.len())
        .map(|i| {
            let name = format_ident!("__evaluation_cells_{i}");
            quote! { self.#name(&mut cells); }
        })
        .collect();

    let one = quote! {
        T::from(stwo::core::fields::m31::BaseField::from_u32_unchecked(1u32))
    };
    let mut constraint_exprs = vec![quote! {
        #enabler * (#one - #enabler)
    }];
    // Per-flag booleanity (structural, ungated) for flag tables — together
    // with the enabler() = flag-sum booleanity this makes the flags one-hot,
    // matching the schema's column-generated constraints.
    for field in &function.table.fields {
        let name = field.to_string();
        if name.starts_with("opcode_") && name.ends_with("_flag") {
            constraint_exprs.push(quote! {
                self.#field.clone() * (#one - self.#field.clone())
            });
        }
    }
    for constraint in &function.constraints {
        // Enabler-gated: padding rows are all-zero, which constant terms in
        // the cell chains would otherwise violate. Cell budgets are
        // max_degree - 1, so the gate stays within the bound.
        let expr = air_expr(constraint, &columns, &cell_indices)?;
        constraint_exprs.push(quote! {
            #enabler * (#expr)
        });
    }
    for constraint in &function.raw_constraints {
        // Ungated `constrain`: vanishes on padding by its own structure.
        let expr = air_expr(constraint, &columns, &cell_indices)?;
        constraint_exprs.push(expr);
    }
    let constraint_pushes: Vec<TokenStream2> = constraint_exprs
        .iter()
        .map(|expr| quote! { constraints.push(#expr); })
        .collect();
    let constraint_chunk_fns: Vec<TokenStream2> = constraint_pushes
        .chunks(CHUNK)
        .enumerate()
        .map(|(i, chunk)| {
            let name = format_ident!("__evaluation_constraints_{i}");
            quote! {
                #[doc(hidden)]
                fn #name(&self, cells: &[T], constraints: &mut Vec<T>) {
                    #(#chunk)*
                }
            }
        })
        .collect();
    let constraint_chunk_calls: Vec<TokenStream2> = (0..constraint_chunk_fns.len())
        .map(|i| {
            let name = format_ident!("__evaluation_constraints_{i}");
            quote! { self.#name(&cells, &mut constraints); }
        })
        .collect();
    let n_constraints = constraint_exprs.len();

    // The calling convention: the own activation tuple with multiplicity
    // -enabler, one tuple per activation made with +enabler.
    let own_values = function.table.fields[..function.n_args]
        .iter()
        .map(|cell| air_expr(&syn::parse_quote!(#cell), &columns, &cell_indices))
        .chain(
            function
                .ret_cells
                .iter()
                .map(|cell| air_expr(&syn::parse_quote!(#cell), &columns, &cell_indices)),
        )
        .collect::<syn::Result<Vec<_>>>()?;
    let mut entry_exprs = vec![quote! {
        (
            (-(#enabler)),
            vec![#(#own_values),*],
        )
    }];
    for (_, args, rets) in &function.calls {
        let values = args
            .iter()
            .chain(rets.iter())
            .map(|cell| air_expr(&syn::parse_quote!(#cell), &columns, &cell_indices))
            .collect::<syn::Result<Vec<_>>>()?;
        entry_exprs.push(quote! {
            (
                #enabler,
                vec![#(#values),*],
            )
        });
    }
    // External relation entries follow the activation entries, in lowering
    // order — the same order `generate_component_module` lists their
    // relation names, so the positional entry→relation mapping holds.
    for (_, cells, emit, mult_cell) in &function.relation_entries {
        let values = cells
            .iter()
            .map(|cell| air_expr(&syn::parse_quote!(#cell), &columns, &cell_indices))
            .collect::<syn::Result<Vec<_>>>()?;
        let mult = match mult_cell {
            Some(cell) => air_expr(&syn::parse_quote!(#cell), &columns, &cell_indices)?,
            None => enabler.clone(),
        };
        let numerator = if *emit {
            mult
        } else {
            quote! { -(#mult) }
        };
        entry_exprs.push(quote! {
            (
                #numerator,
                vec![#(#values),*],
            )
        });
    }

    Ok(quote! {
        impl<T> prover_columns::#columns_type<T>
        where
            T: Clone
                + From<stwo::core::fields::m31::BaseField>
                + core::ops::Add<Output = T>
                + core::ops::Sub<Output = T>
                + core::ops::Mul<Output = T>
                + core::ops::Neg<Output = T>,
        {
            #(#cell_chunk_fns)*

            #(#constraint_chunk_fns)*

            /// Straight-line frame evaluation: (constraints, lookup
            /// entries), the single source for the AIR and the witness.
            #[allow(unused_mut, unused_variables)]
            pub fn evaluation(&self) -> (Vec<T>, Vec<(T, Vec<T>)>) {
                let mut cells: Vec<T> = Vec::with_capacity(#n_cells);
                #(#cell_chunk_calls)*
                let mut constraints: Vec<T> = Vec::with_capacity(#n_constraints);
                #(#constraint_chunk_calls)*
                let entries = vec![#(#entry_exprs),*];
                (constraints, entries)
            }
        }
    })
}

pub fn define_air_fns(input: TokenStream) -> TokenStream {
    let AirFnsInput {
        max_degree,
        embedded,
        embedded_component,
        embedded_enabler_boolean,
        embedded_relations,
        logup_batch,
        embedded_dynamic_component,
        embedded_preprocessed,
        embedded_params,
        relations: external_relations,
        fns,
    } = parse_macro_input!(input as AirFnsInput);

    let relation_arities: HashMap<String, usize> = external_relations
        .iter()
        .map(|(name, arity)| (name.to_string(), *arity))
        .collect();

    let inline_fns: HashMap<String, AirFn> = fns
        .iter()
        .filter(|f| f.inline)
        .map(|f| {
            (
                f.name.to_string(),
                AirFn {
                    inline: true,
                    name: f.name.clone(),
                    params: f
                        .params
                        .iter()
                        .map(|p| Param {
                            name: p.name.clone(),
                            size: p.size,
                        })
                        .collect(),
                    body: clone_body(&f.body),
                    rets: f.rets.clone(),
                },
            )
        })
        .collect();

    // Lower in declaration order: calls reference earlier functions, so
    // flattened arities accumulate as we go.
    let mut arities: HashMap<String, (usize, usize)> = HashMap::new();
    let fixed_params: std::collections::HashSet<String> =
        embedded_params.iter().map(ToString::to_string).collect();
    #[allow(unused_mut)]
    let mut lowered: Vec<LoweredFn> = Vec::new();
    for function in fns.iter().filter(|f| !f.inline) {
        match lower_fn(
            function,
            max_degree,
            &arities,
            &relation_arities,
            &inline_fns,
            embedded.is_some(),
            &fixed_params,
        ) {
            Ok(result) => {
                arities.insert(function.name.to_string(), (result.n_args, result.n_rets));
                lowered.push(result);
            }
            Err(error) => return error.to_compile_error().into(),
        }
    }

    if let Some(flags) = embedded {
        if !embedded_preprocessed.is_empty() {
            if !embedded_component {
                return syn::Error::new(
                    proc_macro2::Span::call_site(),
                    "embedded_preprocessed requires embedded_component: true",
                )
                .to_compile_error()
                .into();
            }
            if !flags.is_empty() {
                return syn::Error::new(
                    proc_macro2::Span::call_site(),
                    "embedded_preprocessed does not accept embedded flag columns",
                )
                .to_compile_error()
                .into();
            }
            return generate_embedded_preprocessed(
                &mut lowered,
                &embedded_relations,
                logup_batch,
                embedded_enabler_boolean,
                &embedded_preprocessed,
                &embedded_params,
            );
        }
        // In embedded mode the declared relations are NOT given their own
        // generated types — `emit`/`consume` map onto the host
        // `crate::relations::Relations` (an opcode emitting `program_access`,
        // `memory_access`, range checks, …). The declarations only fix arity
        // for the parser.
        return generate_embedded(
            &mut lowered,
            &flags,
            embedded_component,
            &embedded_relations,
            logup_batch,
            embedded_dynamic_component,
        );
    }

    // Backend: tables, generic columns, exported lookup macros.
    let tables: Vec<_> = lowered.iter().map(|f| generate_table(&f.table)).collect();
    let prover_columns: Vec<_> = lowered
        .iter()
        .map(|f| generate_prover_columns(&f.table).unwrap_or_else(|e| e.to_compile_error()))
        .collect();
    let evaluation_impls: Vec<_> = lowered
        .iter()
        .map(|f| generate_evaluation_impl(f).unwrap_or_else(|e| e.to_compile_error()))
        .collect();

    // Relations: one io relation per function over (inputs..., outputs...).
    let relation_defs: Vec<_> = lowered
        .iter()
        .map(|f| {
            let relation_type = format_ident!("{}IoRelation", to_pascal_case(&f.name.to_string()));
            let arity = f.n_args + f.n_rets;
            quote! { stwo_constraint_framework::relation!(#relation_type, #arity); }
        })
        .collect();
    let relation_fields: Vec<_> = lowered
        .iter()
        .map(|f| {
            let name = &f.name;
            let relation_type = format_ident!("{}IoRelation", to_pascal_case(&f.name.to_string()));
            quote! { pub #name: #relation_type, }
        })
        .collect();
    let relation_dummy: Vec<_> = lowered
        .iter()
        .map(|f| {
            let name = &f.name;
            let relation_type = format_ident!("{}IoRelation", to_pascal_case(&f.name.to_string()));
            quote! { #name: #relation_type::dummy(), }
        })
        .collect();
    let mut relation_draw: Vec<_> = lowered
        .iter()
        .map(|f| {
            let name = &f.name;
            let relation_type = format_ident!("{}IoRelation", to_pascal_case(&f.name.to_string()));
            quote! { #name: #relation_type::draw(channel), }
        })
        .collect();

    // Externally declared relations: a `relation!` type and an
    // `AirFnRelations` field each, drawn from the channel alongside the io
    // relations. Sharing one relation across two systems is done by drawing
    // it once and passing it in (see the `extern_relation` test).
    let mut relation_defs = relation_defs;
    let mut relation_fields = relation_fields;
    let mut relation_dummy = relation_dummy;
    for (name, arity) in &external_relations {
        let relation_type = format_ident!("{}Relation", to_pascal_case(&name.to_string()));
        relation_defs.push(quote! {
            stwo_constraint_framework::relation!(#relation_type, #arity);
        });
        relation_fields.push(quote! { pub #name: #relation_type, });
        relation_dummy.push(quote! { #name: #relation_type::dummy(), });
        relation_draw.push(quote! { #name: #relation_type::draw(channel), });
    }

    // Tables holder + witness fill functions (the program run concretely).
    let table_fields: Vec<_> = lowered
        .iter()
        .map(|f| {
            let name = &f.name;
            let table_type = table_name(&f.name);
            quote! { pub #name: #table_type, }
        })
        .collect();
    let call_fns: Vec<_> = lowered
        .iter()
        .map(|f| generate_call_fn(f).unwrap_or_else(|e| e.to_compile_error()))
        .collect();

    // Component modules (air + witness) per function.
    let component_modules: Vec<_> = lowered.iter().map(generate_component_module).collect();

    // Prove/verify harness.
    let harness = generate_harness(&lowered);

    quote! {
        #(#tables)*

        pub mod prover_columns {
            #[allow(unused_imports)]
            use stwo_constraint_framework::EvalAtRow;

            #(#prover_columns)*
        }

        #(#evaluation_impls)*

        #(#relation_defs)*

        /// The io relations: one per function, over (inputs..., outputs...).
        #[derive(Clone)]
        pub struct AirFnRelations {
            #(#relation_fields)*
        }

        impl AirFnRelations {
            pub fn dummy() -> Self {
                Self { #(#relation_dummy)* }
            }

            pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
                Self { #(#relation_draw)* }
            }
        }

        /// One table per function; each activation is a row.
        #[derive(Default)]
        pub struct Tables {
            #(#table_fields)*
        }

        #(#call_fns)*

        #(#component_modules)*

        #harness
    }
    .into()
}

/// Embedded mode: a single function generating only the table, the columns
/// struct with `evaluation()`, and the row-fill — for components that live
/// inside a larger system (the host wires relations and proving). Flag
/// columns are appended to the table and exposed on the struct.
/// Generate an embedded component whose function arguments come from trusted
/// preprocessed columns or verifier-supplied field constants. No committed
/// table is emitted: the same lowered frame evaluates the AIR relation entries
/// and the matching interaction trace over the fixed schedule.
fn generate_embedded_preprocessed(
    lowered: &mut [LoweredFn],
    relations_path: &Path,
    logup_batch: usize,
    enabler_boolean: bool,
    preprocessed: &[(Ident, LitStr)],
    params: &[Ident],
) -> TokenStream {
    let [function] = lowered else {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "embedded_preprocessed mode takes exactly one non-inline function",
        )
        .to_compile_error()
        .into();
    };
    if !function.calls.is_empty() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "embedded_preprocessed functions cannot activate other functions",
        )
        .to_compile_error()
        .into();
    }
    if function.table.fields.len() != function.n_args {
        return syn::Error::new(
            function.name.span(),
            "embedded_preprocessed functions must stay within the declared degree budget without materialized intermediates",
        )
        .to_compile_error()
        .into();
    }
    if function.relation_entries.is_empty() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "embedded_preprocessed functions require at least one relation entry",
        )
        .to_compile_error()
        .into();
    }

    let field_names: std::collections::HashSet<String> = function
        .table
        .fields
        .iter()
        .map(ToString::to_string)
        .collect();
    let mut preprocessed_by_name = HashMap::new();
    for (position, (name, id)) in preprocessed.iter().enumerate() {
        if !field_names.contains(&name.to_string()) {
            return syn::Error::new(
                name.span(),
                format!("preprocessed parameter `{name}` is not a function parameter"),
            )
            .to_compile_error()
            .into();
        }
        if preprocessed_by_name
            .insert(name.to_string(), (position, id))
            .is_some()
        {
            return syn::Error::new(name.span(), "duplicate embedded preprocessed parameter")
                .to_compile_error()
                .into();
        }
    }
    let mut param_names = std::collections::HashSet::new();
    for param in params {
        if !field_names.contains(&param.to_string()) {
            return syn::Error::new(
                param.span(),
                format!("embedded parameter `{param}` is not a function parameter"),
            )
            .to_compile_error()
            .into();
        }
        if preprocessed_by_name.contains_key(&param.to_string()) {
            return syn::Error::new(
                param.span(),
                "a function parameter cannot be both preprocessed and verifier-supplied",
            )
            .to_compile_error()
            .into();
        }
        if !param_names.insert(param.to_string()) {
            return syn::Error::new(param.span(), "duplicate embedded parameter")
                .to_compile_error()
                .into();
        }
    }
    // Any remaining function parameters are committed witness columns. The
    // generated table contains only these fields, while the logical columns
    // frame also includes preprocessing and verifier-owned constants.
    let committed_fields: Vec<Ident> = function
        .table
        .fields
        .iter()
        .filter(|field| {
            !preprocessed_by_name.contains_key(&field.to_string())
                && !param_names.contains(&field.to_string())
        })
        .cloned()
        .collect();
    let committed_positions: HashMap<String, usize> = committed_fields
        .iter()
        .enumerate()
        .map(|(position, field)| (field.to_string(), position + 1))
        .collect();
    let has_committed = !committed_fields.is_empty();

    let columns_type = column_struct_name(&function.name);
    let preprocessed_ids: Vec<&LitStr> = preprocessed.iter().map(|(_, id)| id).collect();
    let table = if has_committed {
        let committed_table = OpcodeDef {
            name: function.table.name.clone(),
            fields: committed_fields,
            derived: Vec::new(),
            constraints: Vec::new(),
            lookups: LookupsDef::default(),
            air_only: false,
        };
        generate_table(&committed_table)
    } else {
        quote! {}
    };
    let prover_columns =
        generate_prover_columns(&function.table).unwrap_or_else(|error| error.to_compile_error());
    let evaluation =
        generate_evaluation_impl(function).unwrap_or_else(|error| error.to_compile_error());
    let relations: Vec<&Ident> = function
        .relation_entries
        .iter()
        .map(|(relation, _, _, _)| relation)
        .collect();
    let n_entries = relations.len();
    let indices: Vec<usize> = (0..n_entries).collect();

    let air_values: Vec<TokenStream2> = function
        .table
        .fields
        .iter()
        .map(|field| {
            if let Some((_, id)) = preprocessed_by_name.get(&field.to_string()) {
                quote! {
                    eval.get_preprocessed_column(
                        stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId {
                            id: #id.into(),
                        },
                    )
                }
            } else if param_names.contains(&field.to_string()) {
                quote! { E::F::from(self.#field) }
            } else {
                quote! { eval.next_trace_mask() }
            }
        })
        .collect();
    let witness_values: Vec<TokenStream2> = function
        .table
        .fields
        .iter()
        .map(|field| {
            if let Some((position, _)) = preprocessed_by_name.get(&field.to_string()) {
                quote! { preprocessed[#position].values.data[i] }
            } else if param_names.contains(&field.to_string()) {
                quote! { PackedM31::broadcast(#field) }
            } else {
                let position = committed_positions
                    .get(&field.to_string())
                    .expect("committed field has a trace position");
                quote! { trace[#position].values.data[i] }
            }
        })
        .collect();
    let air_enabler = if has_committed {
        quote! { eval.next_trace_mask() }
    } else {
        quote! { E::F::from(BaseField::from_u32_unchecked(1)) }
    };
    let witness_trace_param = if has_committed {
        quote! {
            trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
        }
    } else {
        quote! {}
    };
    let witness_empty_check = if has_committed {
        quote! { trace.is_empty() || preprocessed.is_empty() }
    } else {
        quote! { preprocessed.is_empty() }
    };
    let witness_enabler = if has_committed {
        quote! { trace[0].values.data[i] }
    } else {
        quote! { PackedM31::broadcast(BaseField::from_u32_unchecked(1)) }
    };
    let witness_size = if has_committed {
        quote! { trace[0].values.data.len() }
    } else {
        quote! { preprocessed[0].values.data.len() }
    };
    let witness_log_size = if has_committed {
        quote! { trace[0].domain.log_size() }
    } else {
        quote! { preprocessed[0].domain.log_size() }
    };

    let constraint_skip = usize::from(!enabler_boolean);
    let finalize_logup = if logup_batch == 2 {
        quote! { eval.finalize_logup_in_pairs(); }
    } else {
        quote! { eval.finalize_logup(); }
    };
    let interaction_columns: Vec<TokenStream2> = indices
        .chunks(logup_batch)
        .map(|batch| match batch {
            [index] => quote! {
                {
                    let mut column = logup_gen.new_col();
                    for (vec_row, (numerator, denominator)) in numerators[#index]
                        .iter()
                        .zip(denominators[#index].iter())
                        .enumerate()
                    {
                        column.write_frac(vec_row, *numerator, *denominator);
                    }
                    column.finalize_col();
                }
            },
            [first, second] => quote! {
                {
                    let mut column = logup_gen.new_col();
                    for vec_row in 0..simd_size {
                        let first_numerator = numerators[#first][vec_row];
                        let first_denominator = denominators[#first][vec_row];
                        let second_numerator = numerators[#second][vec_row];
                        let second_denominator = denominators[#second][vec_row];
                        column.write_frac(
                            vec_row,
                            first_numerator * second_denominator
                                + second_numerator * first_denominator,
                            first_denominator * second_denominator,
                        );
                    }
                    column.finalize_col();
                }
            },
            _ => unreachable!("logup batch is limited to one or two entries"),
        })
        .collect();

    quote! {
        #table

        pub mod prover_columns {
            #[allow(unused_imports)]
            use stwo_constraint_framework::EvalAtRow;

            #prover_columns
        }

        #evaluation

        /// Preprocessed columns in the exact order consumed by the generated
        /// interaction witness.
        pub fn preprocessed_column_ids() -> Vec<
            stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId,
        > {
            vec![
                #(
                    stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId {
                        id: #preprocessed_ids.into(),
                    }
                ),*
            ]
        }

        /// Prover component wiring for a trusted preprocessed schedule.
        pub mod component {
            pub mod air {
                use stwo::core::fields::m31::BaseField;
                use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval};

                use #relations_path as Relations;
                use super::super::prover_columns::#columns_type;

                pub type Component = FrameworkComponent<Eval>;

                #[derive(Clone)]
                pub struct Eval {
                    pub log_size: u32,
                    #(pub #params: BaseField,)*
                    pub relations: Relations,
                }

                impl FrameworkEval for Eval {
                    fn log_size(&self) -> u32 {
                        self.log_size
                    }

                    fn max_constraint_log_degree_bound(&self) -> u32 {
                        self.log_size + 1
                    }

                    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
                        let columns = #columns_type::from_iter([
                            #air_enabler,
                            #(#air_values),*
                        ]);
                        let (constraints, entries) = columns.evaluation();
                        for constraint in constraints.into_iter().skip(#constraint_skip) {
                            eval.add_constraint(constraint);
                        }
                        let mut entries = entries.into_iter();
                        let _ = entries.next();
                        #(
                            {
                                let (multiplicity, values) =
                                    entries.next().expect("relation entry");
                                eval.add_to_relation(
                                    stwo_constraint_framework::RelationEntry::new(
                                        &self.relations.#relations,
                                        multiplicity.into(),
                                        &values,
                                    ),
                                );
                            }
                        )*
                        #finalize_logup
                        eval
                    }
                }
            }

            pub mod witness {
                use num_traits::Zero;
                use stwo::core::ColumnVec;
                use stwo::core::fields::m31::BaseField;
                use stwo::core::fields::qm31::QM31;
                use stwo::prover::backend::simd::SimdBackend;
                use stwo::prover::backend::simd::m31::PackedM31;
                use stwo::prover::backend::simd::qm31::PackedQM31;
                use stwo::prover::poly::BitReversedOrder;
                use stwo::prover::poly::circle::CircleEvaluation;
                use stwo_constraint_framework::{LogupTraceGenerator, Relation};

                use #relations_path as Relations;
                use super::super::prover_columns::#columns_type;

                /// Build interaction columns from the trusted preprocessing and
                /// the same lowered relation entries used by the AIR.
                pub fn gen_interaction_trace(
                    #witness_trace_param
                    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
                    #(#params: BaseField,)*
                    relations: &Relations,
                ) -> (
                    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
                    QM31,
                ) {
                    if #witness_empty_check {
                        return (vec![], QM31::zero());
                    }
                    let simd_size = #witness_size;
                    let log_size = #witness_log_size;
                    let mut logup_gen = LogupTraceGenerator::new(log_size);
                    let mut numerators: Vec<Vec<PackedQM31>> =
                        vec![Vec::with_capacity(simd_size); #n_entries];
                    let mut denominators: Vec<Vec<PackedQM31>> =
                        vec![Vec::with_capacity(simd_size); #n_entries];
                    for i in 0..simd_size {
                        let columns = #columns_type::from_iter([
                            #witness_enabler,
                            #(#witness_values),*
                        ]);
                        let (_, entries) = columns.evaluation();
                        let entries: Vec<_> = entries.into_iter().skip(1).collect();
                        #(
                            {
                                let (multiplicity, values) = &entries[#indices];
                                numerators[#indices].push(PackedQM31::from(*multiplicity));
                                denominators[#indices].push(
                                    Relation::combine(&relations.#relations, values),
                                );
                            }
                        )*
                    }
                    #(#interaction_columns)*
                    logup_gen.finalize_last()
                }
            }
        }
    }
    .into()
}

fn generate_embedded(
    lowered: &mut [LoweredFn],
    flags: &[Ident],
    embedded_component: bool,
    relations_path: &Path,
    logup_batch: usize,
    embedded_dynamic_component: bool,
) -> TokenStream {
    let [function] = lowered else {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "embedded mode takes exactly one (non-inline) function",
        )
        .to_compile_error()
        .into();
    };
    if !function.calls.is_empty() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "embedded functions cannot activate other functions",
        )
        .to_compile_error()
        .into();
    }
    function.table.fields.extend(flags.iter().cloned());

    let table = generate_table(&function.table);
    let prover_columns =
        generate_prover_columns(&function.table).unwrap_or_else(|e| e.to_compile_error());
    let evaluation = generate_evaluation_impl(function).unwrap_or_else(|e| e.to_compile_error());
    let fill = generate_embedded_fill(function, flags).unwrap_or_else(|e| e.to_compile_error());
    let component = if embedded_component {
        if function.relation_entries.is_empty() {
            // No emit/consume statements: the Poseidon2 adapter, which emits
            // from the io activation tuple under its narrow/wide/io flags.
            generate_embedded_poseidon2_component(function, flags, relations_path)
        } else {
            // An opcode: emit its declared relations (emit/consume) against
            // the host `crate::relations::Relations`.
            generate_embedded_opcode_component(
                function,
                relations_path,
                logup_batch,
                embedded_dynamic_component,
            )
        }
    } else {
        quote! {}
    };

    quote! {
        #table

        pub mod prover_columns {
            #[allow(unused_imports)]
            use stwo_constraint_framework::EvalAtRow;

            #prover_columns
        }

        #evaluation

        #fill

        #component
    }
    .into()
}

/// Is a host relation preprocessed (a lookup table whose multiplicities the
/// opcode must register)? In the rv32im relation set these are the range
/// checks and the bitwise table.
fn is_preprocessed_relation(name: &Ident) -> bool {
    let n = name.to_string();
    n.starts_with("range_check") || n == "bitwise"
}

/// The embedded component maps the function's declared relation statements to
/// a host relation bundle and generates matching AIR and witness LogUp paths.
/// The function's own io activation tuple is unused because the host fills the
/// table directly rather than activating it through a function relation.
fn generate_embedded_opcode_component(
    function: &LoweredFn,
    relations_path: &Path,
    logup_batch: usize,
    embedded_dynamic_component: bool,
) -> TokenStream2 {
    let columns_type = column_struct_name(&function.name);
    // SIMD length column: the first committed column (flag tables have no
    // `enabler` column to measure).
    let len_col = function
        .table
        .fields
        .first()
        .cloned()
        .unwrap_or_else(|| format_ident!("enabler"));
    let n_entries = function.relation_entries.len();
    let indices: Vec<usize> = (0..n_entries).collect();
    let relations: Vec<&Ident> = function
        .relation_entries
        .iter()
        .map(|(relation, _, _, _)| relation)
        .collect();

    // Preprocessed entries (range checks / bitwise): their per-row
    // multiplicities feed the preprocessed table's counter.
    let preprocessed: Vec<(usize, &Ident)> = function
        .relation_entries
        .iter()
        .enumerate()
        .filter(|(_, (relation, _, _, _))| is_preprocessed_relation(relation))
        .map(|(index, (relation, _, _, _))| (index, relation))
        .collect();
    let pp_slots: Vec<usize> = (0..preprocessed.len()).collect();
    let pp_entry_indices: Vec<usize> = preprocessed.iter().map(|(i, _)| *i).collect();
    let pp_relations: Vec<&Ident> = preprocessed.iter().map(|(_, r)| *r).collect();
    let n_preprocessed = preprocessed.len();
    let finalize_logup = if logup_batch == 2 {
        quote! { eval.finalize_logup_in_pairs(); }
    } else {
        quote! { eval.finalize_logup(); }
    };
    let interaction_columns: Vec<TokenStream2> = indices
        .chunks(logup_batch)
        .map(|batch| match batch {
            [index] => quote! {
                {
                    let mut col = logup_gen.new_col();
                    for (vec_row, (n, d)) in numerators[#index]
                        .iter()
                        .zip(denominators[#index].iter())
                        .enumerate()
                    {
                        col.write_frac(vec_row, *n, *d);
                    }
                    col.finalize_col();
                }
            },
            [first, second] => quote! {
                {
                    let mut col = logup_gen.new_col();
                    for vec_row in 0..simd_size {
                        let first_numerator = numerators[#first][vec_row];
                        let first_denominator = denominators[#first][vec_row];
                        let second_numerator = numerators[#second][vec_row];
                        let second_denominator = denominators[#second][vec_row];
                        col.write_frac(
                            vec_row,
                            first_numerator * second_denominator
                                + second_numerator * first_denominator,
                            first_denominator * second_denominator,
                        );
                    }
                    col.finalize_col();
                }
            },
            _ => unreachable!("logup batch is limited to one or two entries"),
        })
        .collect();
    let register_multiplicities = if preprocessed.is_empty() {
        quote! {
            /// This component has no preprocessed lookup multiplicities.
            pub fn register_multiplicities<T>(
                _trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
                _counters: &mut T,
            ) {
            }
        }
    } else {
        quote! {
            /// Register preprocessed multiplicities for range-check and bitwise lookups.
            pub fn register_multiplicities(
                trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
                counters: &mut crate::relations::Counters,
            ) {
                if trace.is_empty() {
                    return;
                }
                let _ = (&counters,);
                let cols = #columns_type::from_iter(trace.iter().map(|eval| &eval.values.data));
                let simd_size = cols.#len_col.len();
                let mut multiplicities: Vec<Vec<stwo::prover::backend::simd::m31::PackedM31>> =
                    vec![Vec::with_capacity(simd_size); #n_preprocessed];
                let mut elements: Vec<Vec<Vec<stwo::prover::backend::simd::m31::PackedM31>>> =
                    Vec::with_capacity(#n_preprocessed);
                for _ in 0..#n_preprocessed {
                    elements.push(Vec::new());
                }
                for i in 0..simd_size {
                    let (_, entries) = cols.at(i).evaluation();
                    let entries: Vec<_> = entries.into_iter().skip(1).collect();
                    #(
                        {
                            let (multiplicity, values) = &entries[#pp_entry_indices];
                            multiplicities[#pp_slots].push(*multiplicity);
                            if elements[#pp_slots].is_empty() {
                                for _ in 0..values.len() {
                                    elements[#pp_slots].push(Vec::with_capacity(simd_size));
                                }
                            }
                            for (column, value) in
                                elements[#pp_slots].iter_mut().zip(values.iter())
                            {
                                column.push(*value);
                            }
                        }
                    )*
                }
                #(
                    counters.#pp_relations.register_many(
                        &multiplicities[#pp_slots],
                        &elements[#pp_slots]
                            .iter()
                            .map(|column| column.as_slice())
                            .collect::<Vec<_>>(),
                    );
                )*
            }
        }
    };
    let dynamic_eval = if embedded_dynamic_component {
        quote! {
            impl air::relation_eval::DynamicRelationFrameworkEval for Eval {
                fn evaluate_dynamic_relations<E: air::relation_eval::DynamicRelationEvalAtRow>(
                    &self,
                    mut eval: E,
                ) -> E {
                    let cols = #columns_type::from_eval(&mut eval);
                    let (constraints, entries) = cols.evaluation();
                    for constraint in constraints {
                        eval.add_constraint(constraint);
                    }
                    let mut entries = entries.into_iter();
                    let _ = entries.next();
                    #(
                        {
                            let (multiplicity, values) =
                                entries.next().expect("relation entry");
                            eval.add_to_named_relation(
                                stringify!(#relations),
                                multiplicity.into(),
                                &values,
                            );
                        }
                    )*
                    #finalize_logup
                    eval
                }
            }
        }
    } else {
        quote! {}
    };

    quote! {
        /// Prover component wiring for the embedded opcode.
        pub mod component {
            pub mod air {
                use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval};

                use #relations_path as Relations;
                use super::super::prover_columns::#columns_type;

                pub type Component = FrameworkComponent<Eval>;

                #[derive(Clone)]
                pub struct Eval {
                    pub log_size: u32,
                    pub relations: Relations,
                }

                impl FrameworkEval for Eval {
                    fn log_size(&self) -> u32 {
                        self.log_size
                    }

                    fn max_constraint_log_degree_bound(&self) -> u32 {
                        self.log_size + 1
                    }

                    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
                        let cols = #columns_type::from_eval(&mut eval);
                        let (constraints, entries) = cols.evaluation();
                        for constraint in constraints {
                            eval.add_constraint(constraint);
                        }
                        let mut entries = entries.into_iter();
                        // Entry 0 is the function's own io activation tuple,
                        // unused: the opcode emits the host relations instead.
                        let _ = entries.next();
                        #(
                            {
                                let (multiplicity, values) =
                                    entries.next().expect("relation entry");
                                eval.add_to_relation(
                                    stwo_constraint_framework::RelationEntry::new(
                                        &self.relations.#relations,
                                        multiplicity.into(),
                                        &values,
                                    ),
                                );
                            }
                        )*
                        #finalize_logup
                        eval
                    }
                }

                #dynamic_eval
            }

            pub mod witness {
                use num_traits::Zero;
                use stwo::core::ColumnVec;
                use stwo::core::fields::m31::BaseField;
                use stwo::core::fields::qm31::QM31;
                use stwo::prover::backend::simd::SimdBackend;
                use stwo::prover::backend::simd::qm31::PackedQM31;
                use stwo::prover::poly::BitReversedOrder;
                use stwo::prover::poly::circle::CircleEvaluation;
                use stwo_constraint_framework::{LogupTraceGenerator, Relation};

                use #relations_path as Relations;
                use super::super::prover_columns::#columns_type;

                /// Interaction columns use the same relation order and batch
                /// shape as the generated AIR.
                pub fn gen_interaction_trace(
                    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
                    relations: &Relations,
                ) -> (
                    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
                    QM31,
                ) {
                    if trace.is_empty() {
                        return (vec![], QM31::zero());
                    }
                    let cols = #columns_type::from_iter(trace.iter().map(|eval| &eval.values.data));
                    let simd_size = cols.#len_col.len();
                    let log_size = trace[0].domain.log_size();
                    let mut logup_gen = LogupTraceGenerator::new(log_size);

                    let mut numerators: Vec<Vec<PackedQM31>> =
                        vec![Vec::with_capacity(simd_size); #n_entries];
                    let mut denominators: Vec<Vec<PackedQM31>> =
                        vec![Vec::with_capacity(simd_size); #n_entries];
                    for i in 0..simd_size {
                        let (_, entries) = cols.at(i).evaluation();
                        // Skip entry 0 (the io activation tuple).
                        let entries: Vec<_> = entries.into_iter().skip(1).collect();
                        #(
                            {
                                let (multiplicity, values) = &entries[#indices];
                                numerators[#indices].push(PackedQM31::from(*multiplicity));
                                denominators[#indices].push(
                                    Relation::combine(&relations.#relations, values),
                                );
                            }
                        )*
                    }
                    #(#interaction_columns)*
                    logup_gen.finalize_last()
                }

                #register_multiplicities
            }
        }
    }
}

/// LogUp adapter for embedded Poseidon2: narrow, wide, and atomic io modes.
fn generate_embedded_poseidon2_component(
    function: &LoweredFn,
    flags: &[Ident],
    relations_path: &Path,
) -> TokenStream2 {
    let _ = flags;
    let columns_type = column_struct_name(&function.name);
    quote! {
        /// Prover component wiring for the embedded Poseidon2 permutation.
        pub mod component {
            pub mod air {
                use num_traits::One;
                use crate::relation_eval::{
                    DynamicRelationEvalAtRow, DynamicRelationFrameworkEval,
                };
                use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry};

                use #relations_path as Relations;
                use super::super::prover_columns::#columns_type;

                pub type Component = FrameworkComponent<Eval>;

                #[derive(Clone)]
                pub struct Eval {
                    pub log_size: u32,
                    pub relations: Relations,
                }

                impl FrameworkEval for Eval {
                    fn log_size(&self) -> u32 {
                        self.log_size
                    }

                    fn max_constraint_log_degree_bound(&self) -> u32 {
                        self.log_size + 1
                    }

                    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
                        let cols = #columns_type::from_eval(&mut eval);
                        let (constraints, entries) = cols.evaluation();
                        for constraint in constraints {
                            eval.add_constraint(constraint);
                        }

                        let one = E::F::one();
                        let enabler = cols.enabler.clone();
                        let wide = cols.wide.clone();
                        let io = cols.io.clone();
                        eval.add_constraint(wide.clone() * (one.clone() - wide.clone()));
                        eval.add_constraint(io.clone() * (one.clone() - io.clone()));
                        eval.add_constraint(wide.clone() * io.clone());

                        let (_, tuple) = entries
                            .into_iter()
                            .next()
                            .expect("the felt function has one activation tuple");
                        let (input, output) = tuple.split_at(16);

                        eval.add_to_relation(RelationEntry::new(
                            &self.relations.poseidon2,
                            (-(enabler.clone() * (one.clone() - io.clone()))).into(),
                            input,
                        ));
                        eval.add_to_relation(RelationEntry::new(
                            &self.relations.poseidon2,
                            (enabler.clone() * (one.clone() - wide.clone() - io.clone())).into(),
                            &output[..1],
                        ));
                        eval.add_to_relation(RelationEntry::new(
                            &self.relations.poseidon2,
                            (enabler.clone() * wide).into(),
                            &output[..8],
                        ));
                        eval.add_to_relation(RelationEntry::new(
                            &self.relations.poseidon2_io,
                            (enabler * io).into(),
                            &tuple,
                        ));
                        eval.finalize_logup_in_pairs();
                        eval
                    }
                }

                impl DynamicRelationFrameworkEval for Eval {
                    fn evaluate_dynamic_relations<E: DynamicRelationEvalAtRow>(
                        &self,
                        mut eval: E,
                    ) -> E {
                        let cols = #columns_type::from_eval(&mut eval);
                        let (constraints, entries) = cols.evaluation();
                        for constraint in constraints {
                            eval.add_constraint(constraint);
                        }

                        let one = E::F::one();
                        let enabler = cols.enabler.clone();
                        let wide = cols.wide.clone();
                        let io = cols.io.clone();
                        eval.add_constraint(wide.clone() * (one.clone() - wide.clone()));
                        eval.add_constraint(io.clone() * (one.clone() - io.clone()));
                        eval.add_constraint(wide.clone() * io.clone());

                        let (_, tuple) = entries
                            .into_iter()
                            .next()
                            .expect("the felt function has one activation tuple");
                        let (input, output) = tuple.split_at(16);

                        eval.add_to_named_relation(
                            stringify!(poseidon2),
                            (-(enabler.clone() * (one.clone() - io.clone()))).into(),
                            input,
                        );
                        eval.add_to_named_relation(
                            stringify!(poseidon2),
                            (enabler.clone() * (one.clone() - wide.clone() - io.clone())).into(),
                            &output[..1],
                        );
                        eval.add_to_named_relation(
                            stringify!(poseidon2),
                            (enabler.clone() * wide).into(),
                            &output[..8],
                        );
                        eval.add_to_named_relation(
                            stringify!(poseidon2_io),
                            (enabler * io).into(),
                            &tuple,
                        );
                        eval.finalize_logup_in_pairs();
                        eval
                    }
                }
            }

            pub mod witness {
                use num_traits::{One, Zero};
                use stwo::core::ColumnVec;
                use stwo::core::fields::m31::BaseField;
                use stwo::core::fields::qm31::QM31;
                use stwo::prover::backend::simd::SimdBackend;
                use stwo::prover::backend::simd::m31::PackedM31;
                use stwo::prover::backend::simd::qm31::PackedQM31;
                use stwo::prover::poly::BitReversedOrder;
                use stwo::prover::poly::circle::CircleEvaluation;
                use stwo_constraint_framework::{LogupTraceGenerator, Relation};

                use crate::relations::Counters;
                use #relations_path as Relations;
                use super::super::prover_columns::#columns_type;

                pub fn gen_interaction_trace(
                    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
                    relations: &Relations,
                ) -> (
                    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
                    QM31,
                ) {
                    if trace.is_empty() {
                        return (vec![], QM31::zero());
                    }
                    let cols = #columns_type::from_iter(trace.iter().map(|eval| &eval.values.data));
                    let simd_size = cols.enabler.len();
                    let log_size = trace[0].domain.log_size();
                    let mut logup_gen = LogupTraceGenerator::new(log_size);

                    let one = PackedM31::one();
                    let mut consume_input = Vec::with_capacity(simd_size);
                    let mut input_denoms: Vec<PackedQM31> = Vec::with_capacity(simd_size);
                    let mut emit_narrow = Vec::with_capacity(simd_size);
                    let mut narrow_denoms: Vec<PackedQM31> = Vec::with_capacity(simd_size);
                    let mut emit_wide = Vec::with_capacity(simd_size);
                    let mut wide_denoms: Vec<PackedQM31> = Vec::with_capacity(simd_size);
                    let mut emit_io = Vec::with_capacity(simd_size);
                    let mut io_denoms: Vec<PackedQM31> = Vec::with_capacity(simd_size);
                    for i in 0..simd_size {
                        let (_, entries) = cols.at(i).evaluation();
                        let (_, tuple) = entries.into_iter().next().expect("one activation tuple");
                        let enabler = cols.enabler[i];
                        let wide = cols.wide[i];
                        let io = cols.io[i];
                        consume_input.push(-PackedQM31::from(enabler * (one - io)));
                        input_denoms.push(relations.poseidon2.combine(&tuple[..16]));
                        emit_narrow.push(PackedQM31::from(enabler * (one - wide - io)));
                        narrow_denoms.push(relations.poseidon2.combine(&tuple[16..17]));
                        emit_wide.push(PackedQM31::from(enabler * wide));
                        wide_denoms.push(relations.poseidon2.combine(&tuple[16..24]));
                        emit_io.push(PackedQM31::from(enabler * io));
                        io_denoms.push(relations.poseidon2_io.combine(&tuple));
                    }

                    stwo_macros::write_pair!(
                        &consume_input,
                        &input_denoms,
                        &emit_narrow,
                        &narrow_denoms,
                        logup_gen
                    );
                    stwo_macros::write_pair!(&emit_wide, &wide_denoms, &emit_io, &io_denoms, logup_gen);
                    logup_gen.finalize_last()
                }

                pub fn register_multiplicities(
                    _trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
                    _counters: &mut Counters,
                ) {
                }
            }
        }
    }
}

/// The embedded row-fill: run the cells, push the row (flags appended),
/// return the outputs.
fn generate_embedded_fill(function: &LoweredFn, flags: &[Ident]) -> syn::Result<TokenStream2> {
    let name = &function.name;
    let fn_name = format_ident!("{}_fill", name);
    let table_type = table_name(name);
    let n_args = function.n_args;
    let n_rets = function.n_rets;
    let n_flags = flags.len();
    let arg_cells: Vec<&Ident> = function.table.fields[..n_args].iter().collect();

    let mut steps: Vec<TokenStream2> = Vec::new();
    for step in &function.fill {
        match step {
            FillStep::Expr { cell, expr } => {
                let value = concrete_expr(expr)?;
                steps.push(quote! { let #cell = #value; });
            }
            FillStep::Call { .. } => unreachable!("embedded functions make no calls"),
        }
    }

    // Row layout: the leading `enabler` column (1 for filled rows) exists
    // only on non-flag tables — flag tables synthesize `enabler()` from the
    // opcode flags and have no enabler column. Then the lowered fields, then
    // the embedded flags.
    let mut row_values: Vec<TokenStream2> = if count_opcode_flags(&function.table.fields) == 0 {
        vec![quote!(1u32)]
    } else {
        vec![]
    };
    for field in &function.table.fields[..function.table.fields.len() - n_flags] {
        row_values.push(quote!(#field.0));
    }
    for position in 0..n_flags {
        row_values.push(quote!(flags[#position]));
    }
    let ret_cells = &function.ret_cells;

    let doc = format!(
        "Run `{name}` over the arguments, push the trace row (with the flag          columns appended), and return the outputs."
    );
    Ok(quote! {
        #[doc = #doc]
        // Cells used only in relation tuples / constraints are recomputed in
        // the AIR's `evaluation()`, so their fill bindings can be unused here.
        #[allow(unused_variables)]
        pub fn #fn_name(
            table: &mut #table_type,
            args: [stwo::core::fields::m31::BaseField; #n_args],
            flags: [u32; #n_flags],
        ) -> [stwo::core::fields::m31::BaseField; #n_rets] {
            let enabler = stwo::core::fields::m31::BaseField::from_u32_unchecked(1);
            let [#(#arg_cells),*] = args;
            #(#steps)*
            table.push_row(&[#(#row_values),*]);
            [#(#ret_cells),*]
        }
    })
}

/// The witness fill: run the lowered cells over `BaseField`, recursively
/// activate callees, push the row, return the outputs.
fn generate_call_fn(function: &LoweredFn) -> syn::Result<TokenStream2> {
    let name = &function.name;
    let fn_name = format_ident!("call_{}", name);
    let n_args = function.n_args;
    let n_rets = function.n_rets;
    let arg_cells: Vec<&Ident> = function.table.fields[..n_args].iter().collect();

    let mut steps: Vec<TokenStream2> = Vec::new();
    for step in &function.fill {
        match step {
            FillStep::Expr { cell, expr } => {
                let value = concrete_expr(expr)?;
                steps.push(quote! { let #cell = #value; });
            }
            FillStep::Call { rets, callee, args } => {
                let callee_fn = format_ident!("call_{}", callee);
                steps.push(quote! {
                    let [#(#rets),*] = #callee_fn(tables, [#(#args),*]);
                });
            }
        }
    }

    // Row layout: enabler then the table fields, in order.
    let mut row_values: Vec<TokenStream2> = vec![quote!(1u32)];
    for field in &function.table.fields {
        row_values.push(quote!(#field.0));
    }
    let ret_cells = &function.ret_cells;

    let doc =
        format!("Activate `{name}`: run the body, recursively activate callees, push the row.");
    Ok(quote! {
        #[doc = #doc]
        // Cells used only in relation tuples / constraints are recomputed in
        // the AIR's `evaluation()`, so their fill bindings can be unused here.
        #[allow(unused_variables)]
        pub fn #fn_name(
            tables: &mut Tables,
            args: [stwo::core::fields::m31::BaseField; #n_args],
        ) -> [stwo::core::fields::m31::BaseField; #n_rets] {
            let enabler = stwo::core::fields::m31::BaseField::from_u32_unchecked(1);
            let [#(#arg_cells),*] = args;
            #(#steps)*
            tables.#name.push_row(&[#(#row_values),*]);
            [#(#ret_cells),*]
        }
    })
}

/// The component module: the AIR and the witness both consume the
/// straight-line `evaluation()` — constraints, then the activation entries
/// bound to the generated relations.
fn generate_component_module(function: &LoweredFn) -> TokenStream2 {
    let name = &function.name;
    let columns_type = column_struct_name(name);
    let n_entries = 1 + function.calls.len() + function.relation_entries.len();
    let entry_indices: Vec<usize> = (0..n_entries).collect();
    let entry_relations: Vec<&Ident> = std::iter::once(&function.name)
        .chain(function.calls.iter().map(|(callee, _, _)| callee))
        .chain(
            function
                .relation_entries
                .iter()
                .map(|(relation, _, _, _)| relation),
        )
        .collect();
    let doc = format!("{name} component, generated from its felt function.");
    quote! {
        #[doc = #doc]
        pub mod #name {
            pub mod air {
                use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval};

                use super::super::AirFnRelations;
                use super::super::prover_columns::#columns_type;

                pub type Component = FrameworkComponent<Eval>;

                #[derive(Clone)]
                pub struct Eval {
                    pub log_size: u32,
                    pub relations: AirFnRelations,
                }

                impl FrameworkEval for Eval {
                    fn log_size(&self) -> u32 {
                        self.log_size
                    }

                    fn max_constraint_log_degree_bound(&self) -> u32 {
                        self.log_size + 1
                    }

                    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
                        let cols = #columns_type::from_eval(&mut eval);
                        let (constraints, entries) = cols.evaluation();
                        for constraint in constraints {
                            eval.add_constraint(constraint);
                        }
                        let mut entries = entries.into_iter();
                        #(
                            {
                                let (multiplicity, values) =
                                    entries.next().expect("one tuple per entry");
                                eval.add_to_relation(
                                    stwo_constraint_framework::RelationEntry::new(
                                        &self.relations.#entry_relations,
                                        multiplicity.into(),
                                        &values,
                                    ),
                                );
                            }
                        )*
                        eval.finalize_logup();
                        eval
                    }
                }
            }

            pub mod witness {
                use num_traits::Zero;
                use stwo::core::ColumnVec;
                use stwo::core::fields::m31::BaseField;
                use stwo::core::fields::qm31::QM31;
                use stwo::prover::backend::simd::SimdBackend;
                use stwo::prover::backend::simd::qm31::PackedQM31;
                use stwo::prover::poly::BitReversedOrder;
                use stwo::prover::poly::circle::CircleEvaluation;
                use stwo_constraint_framework::LogupTraceGenerator;

                use super::super::AirFnRelations;
                use super::super::prover_columns::#columns_type;

                /// One singleton fraction column per activation entry, in
                /// the same order the AIR adds them.
                pub fn gen_interaction_trace(
                    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
                    relations: &AirFnRelations,
                ) -> (
                    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
                    QM31,
                ) {
                    if trace.is_empty() {
                        return (vec![], QM31::zero());
                    }
                    let cols = #columns_type::from_iter(trace.iter().map(|eval| &eval.values.data));
                    let simd_size = cols.enabler.len();
                    let log_size = trace[0].domain.log_size();
                    let mut logup_gen = LogupTraceGenerator::new(log_size);

                    let mut numerators: Vec<Vec<PackedQM31>> =
                        vec![Vec::with_capacity(simd_size); #n_entries];
                    let mut denominators: Vec<Vec<PackedQM31>> =
                        vec![Vec::with_capacity(simd_size); #n_entries];
                    for i in 0..simd_size {
                        let (_, entries) = cols.at(i).evaluation();
                        #(
                            {
                                let (multiplicity, values) = &entries[#entry_indices];
                                numerators[#entry_indices].push(PackedQM31::from(*multiplicity));
                                denominators[#entry_indices].push(
                                    stwo_constraint_framework::Relation::combine(
                                        &relations.#entry_relations,
                                        values,
                                    ),
                                );
                            }
                        )*
                    }
                    #(
                        {
                            let mut col = logup_gen.new_col();
                            for (vec_row, (n, d)) in numerators[#entry_indices]
                                .iter()
                                .zip(denominators[#entry_indices].iter())
                                .enumerate()
                            {
                                col.write_frac(vec_row, *n, *d);
                            }
                            col.finalize_col();
                        }
                    )*
                    logup_gen.finalize_last()
                }
            }
        }
    }
}

/// The prove/verify harness over all function components: single main tree,
/// relations drawn after commit, interaction traces, public activation
/// terms, stwo prove/verify.
fn generate_harness(lowered: &[LoweredFn]) -> TokenStream2 {
    let n_fns = lowered.len();
    let names: Vec<_> = lowered.iter().map(|f| f.name.clone()).collect();
    let indices: Vec<usize> = (0..n_fns).collect();

    let activation_variants: Vec<_> = lowered
        .iter()
        .map(|f| {
            let variant = format_ident!("{}", to_pascal_case(&f.name.to_string()));
            let n_args = f.n_args;
            let n_rets = f.n_rets;
            quote! {
                #variant {
                    inputs: [stwo::core::fields::m31::BaseField; #n_args],
                    outputs: [stwo::core::fields::m31::BaseField; #n_rets],
                },
            }
        })
        .collect();
    let activation_term_arms: Vec<_> = lowered
        .iter()
        .map(|f| {
            let name = &f.name;
            let variant = format_ident!("{}", to_pascal_case(&f.name.to_string()));
            quote! {
                Activation::#variant { inputs, outputs } => {
                    let tuple: Vec<stwo::core::fields::m31::BaseField> =
                        inputs.iter().chain(outputs.iter()).copied().collect();
                    let denom: stwo::core::fields::qm31::SecureField =
                        stwo_constraint_framework::Relation::combine(&relations.#name, &tuple);
                    total += stwo::core::fields::FieldExpOps::inverse(&denom);
                }
            }
        })
        .collect();
    let activation_mix_arms: Vec<_> = lowered
        .iter()
        .enumerate()
        .map(|(index, f)| {
            let variant = format_ident!("{}", to_pascal_case(&f.name.to_string()));
            let tag = index as u32;
            quote! {
                Activation::#variant { inputs, outputs } => {
                    channel.mix_u32s(&[#tag]);
                    channel.mix_u32s(&inputs.map(|v| v.0));
                    channel.mix_u32s(&outputs.map(|v| v.0));
                }
            }
        })
        .collect();

    let column_sizes: Vec<_> = lowered
        .iter()
        .map(|f| {
            let columns_type = column_struct_name(&f.name);
            quote! { prover_columns::#columns_type::<()>::SIZE }
        })
        .collect();
    // One singleton fraction column per entry: the own activation, one per
    // call made, and one per external relation emit/consume.
    let entry_counts: Vec<usize> = lowered
        .iter()
        .map(|f| 1 + f.calls.len() + f.relation_entries.len())
        .collect();

    quote! {
        /// A public activation: the io tuple of an entry call the host
        /// performed. The verifier emits these (the rows consume them), so
        /// the LogUp multiset closes over exactly the requested work.
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub enum Activation {
            #(#activation_variants)*
        }

        /// The public side of the activation multiset.
        pub fn public_activation_terms(
            activations: &[Activation],
            relations: &AirFnRelations,
        ) -> stwo::core::fields::qm31::SecureField {
            use num_traits::Zero;
            let mut total = stwo::core::fields::qm31::SecureField::zero();
            for activation in activations {
                match activation {
                    #(#activation_term_arms)*
                }
            }
            total
        }

        fn mix_activations(
            channel: &mut impl stwo::core::channel::Channel,
            activations: &[Activation],
        ) {
            channel.mix_u32s(&[activations.len() as u32]);
            for activation in activations {
                match activation {
                    #(#activation_mix_arms)*
                }
            }
        }

        /// Proof of the function system plus its public claim.
        pub struct AirFnsProof<H: stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted> {
            pub log_sizes: [u32; #n_fns],
            pub sums: [stwo::core::fields::qm31::SecureField; #n_fns],
            pub activations: Vec<Activation>,
            pub stark_proof: stwo::core::proof::StarkProof<H>,
        }

        fn build_components(
            location_allocator: &mut stwo_constraint_framework::TraceLocationAllocator,
            log_sizes: &[u32; #n_fns],
            sums: &[stwo::core::fields::qm31::SecureField; #n_fns],
            relations: &AirFnRelations,
        ) -> Vec<Box<dyn stwo::prover::ComponentProver<stwo::prover::backend::simd::SimdBackend>>> {
            vec![
                #(
                    Box::new(#names::air::Component::new(
                        location_allocator,
                        #names::air::Eval {
                            log_size: log_sizes[#indices],
                            relations: relations.clone(),
                        },
                        sums[#indices],
                    )),
                )*
            ]
        }

        /// Prove the activations: every requested call (and transitively
        /// every internal one) is a row whose constraints hold and whose io
        /// tuple closes the multiset.
        pub fn prove_air_fns(
            tables: Tables,
            activations: Vec<Activation>,
            config: stwo::core::pcs::PcsConfig,
        ) -> AirFnsProof<
            <stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel as stwo::core::channel::MerkleChannel>::H,
        > {
            use stwo::core::channel::{Channel, MerkleChannel};
            use stwo::core::poly::circle::CanonicCoset;
            use stwo::prover::poly::circle::PolyOps;

            type MC = stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
            type B = stwo::prover::backend::simd::SimdBackend;

            let traces = [#(tables.#names.into_witness()),*];
            let log_sizes: [u32; #n_fns] = std::array::from_fn(|i| {
                traces[i]
                    .first()
                    .map(|t| t.domain.log_size())
                    .expect("padded trace is never empty")
            });
            let max_log_size = *log_sizes.iter().max().expect("at least one function");

            let twiddles = B::precompute_twiddles(
                CanonicCoset::new(max_log_size + 2 + config.fri_config.log_blowup_factor)
                    .circle_domain()
                    .half_coset,
            );
            let channel = &mut <MC as MerkleChannel>::C::default();
            let mut commitment_scheme =
                stwo::prover::pcs::CommitmentSchemeProver::<B, MC>::new(config, &twiddles);

            // Tree 0: empty preprocessed trace.
            let mut tree_builder = commitment_scheme.tree_builder();
            tree_builder.extend_evals(vec![]);
            tree_builder.commit(channel);

            channel.mix_u32s(&log_sizes);
            mix_activations(channel, &activations);

            // Tree 1: all function tables in declaration order.
            let mut tree_builder = commitment_scheme.tree_builder();
            tree_builder.extend_evals(traces.iter().flatten().cloned().collect::<Vec<_>>());
            tree_builder.commit(channel);

            let relations = AirFnRelations::draw(channel);

            let mut sums = [stwo::core::fields::qm31::SecureField::default(); #n_fns];
            let mut interaction_columns = Vec::new();
            #(
                {
                    let (columns, sum) =
                        #names::witness::gen_interaction_trace(&traces[#indices], &relations);
                    interaction_columns.extend(columns);
                    sums[#indices] = sum;
                }
            )*
            channel.mix_felts(&sums);

            // Tree 2: interaction traces.
            let mut tree_builder = commitment_scheme.tree_builder();
            tree_builder.extend_evals(interaction_columns);
            tree_builder.commit(channel);

            let mut location_allocator = stwo_constraint_framework::TraceLocationAllocator::default();
            let components = build_components(&mut location_allocator, &log_sizes, &sums, &relations);
            let component_refs: Vec<&dyn stwo::prover::ComponentProver<B>> =
                components.iter().map(|c| c.as_ref()).collect();

            let stark_proof = stwo::prover::prove(&component_refs, channel, commitment_scheme)
                .expect("air fns proof generation failed");

            AirFnsProof {
                log_sizes,
                sums,
                activations,
                stark_proof,
            }
        }

        /// Verify: the claimed sums plus the public activation terms must
        /// cancel, and the stwo proof must hold.
        pub fn verify_air_fns(
            proof: AirFnsProof<
                <stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel as stwo::core::channel::MerkleChannel>::H,
            >,
            config: stwo::core::pcs::PcsConfig,
        ) -> Result<(), stwo::core::verifier::VerificationError> {
            use num_traits::Zero;
            use stwo::core::channel::{Channel, MerkleChannel};

            type MC = stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;

            let channel = &mut <MC as MerkleChannel>::C::default();
            let mut commitment_scheme =
                stwo::core::pcs::CommitmentSchemeVerifier::<MC>::new(config);

            let commitments = &proof.stark_proof.commitments;
            commitment_scheme.commit(commitments[0], &[], channel);
            channel.mix_u32s(&proof.log_sizes);
            mix_activations(channel, &proof.activations);

            let column_log_sizes: Vec<u32> = [#(#column_sizes),*]
                .iter()
                .zip(proof.log_sizes.iter())
                .flat_map(|(&width, &log_size)| std::iter::repeat_n(log_size, width))
                .collect();
            commitment_scheme.commit(commitments[1], &column_log_sizes, channel);

            let relations = AirFnRelations::draw(channel);

            // Every activation tuple consumed by a row must be emitted by a
            // caller row or publicly: the multiset closes exactly over the
            // requested activations.
            let total = proof.sums.iter().copied().sum::<stwo::core::fields::qm31::SecureField>()
                + public_activation_terms(&proof.activations, &relations);
            if !total.is_zero() {
                return Err(stwo::core::verifier::VerificationError::InvalidStructure(
                    "activation multiset does not close over the public activations".to_string(),
                ));
            }
            channel.mix_felts(&proof.sums);

            let interaction_log_sizes: Vec<u32> = [#(#entry_counts),*]
                .iter()
                .zip(proof.log_sizes.iter())
                .flat_map(|(&entries, &log_size)| std::iter::repeat_n(log_size, entries * 4))
                .collect();
            commitment_scheme.commit(commitments[2], &interaction_log_sizes, channel);

            let mut location_allocator = stwo_constraint_framework::TraceLocationAllocator::default();
            let components = build_components(
                &mut location_allocator,
                &proof.log_sizes,
                &proof.sums,
                &relations,
            );
            let verifier_refs: Vec<&dyn stwo::core::air::Component> = components
                .iter()
                .map(|c| c.as_ref() as &dyn stwo::core::air::Component)
                .collect();

            stwo::core::verifier::verify(&verifier_refs, channel, &mut commitment_scheme, proof.stark_proof)
        }
    }
}
