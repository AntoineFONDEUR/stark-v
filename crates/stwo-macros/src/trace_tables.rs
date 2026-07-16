//! Proc-macros for the runner crate.
//!
//! Provides:
//! - `define_trace_tables!` macro for generating columnar trace tables

use std::collections::HashMap;

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{Expr, Ident, Token, braced, parse_macro_input};

use crate::relations::RelationDef;

// =============================================================================
// define_trace_tables! proc-macro
// =============================================================================

/// A derived (computed) column: `name: col_a + pow2(4) * col_b`.
///
/// The expression names trace columns or previously defined derived columns
/// directly. It is compiled once into a generic method usable both in AIR
/// constraints (`T = E::F`) and in witness generation (`T = PackedM31` via
/// `at(i)`).
pub(crate) struct DerivedDef {
    pub(crate) name: Ident,
    pub(crate) expr: Expr,
}

impl Parse for DerivedDef {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let name: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let expr: Expr = input.parse()?;
        Ok(DerivedDef { name, expr })
    }
}

/// One LogUp lookup entry, written exactly like the spec:
/// `multiplicity * relation_name(elem, ...)` (or a bare
/// `relation_name(elem, ...)` for multiplicity 1), optionally prefixed with
/// `preprocessed` when the relation is a preprocessed table whose
/// consumption multiplicities must be registered.
///
/// Multiplicity and element expressions use the derived-expression language
/// with every trace column and derived column in scope (the tuple itself
/// lists what the entry reads, so a separate dependency list would be redundant).
pub(crate) struct LookupEntry {
    pub(crate) preprocessed: bool,
    pub(crate) relation: Ident,
    pub(crate) multiplicity: Expr,
    pub(crate) values: Vec<Expr>,
}

/// Split a lookup entry expression into (multiplicity, relation, tuple):
/// the relation call is the rightmost factor; everything multiplying it
/// (with its sign) is the multiplicity.
fn decompose_lookup_entry(expr: Expr) -> syn::Result<(Expr, Ident, Vec<Expr>)> {
    match expr {
        Expr::Call(call) => {
            let Expr::Path(func) = call.func.as_ref() else {
                return Err(syn::Error::new_spanned(
                    call.func,
                    "lookup entries call a relation by name",
                ));
            };
            let relation = func.path.require_ident()?.clone();
            Ok((
                syn::parse_quote!(1),
                relation,
                call.args.into_iter().collect(),
            ))
        }
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_)) => {
            let (multiplicity, relation, values) = decompose_lookup_entry(*unary.expr)?;
            Ok((syn::parse_quote!(-(#multiplicity)), relation, values))
        }
        Expr::Binary(binary) if matches!(binary.op, syn::BinOp::Mul(_)) => {
            let left = *binary.left;
            let (multiplicity, relation, values) = decompose_lookup_entry(*binary.right)?;
            let multiplicity = if matches!(
                &multiplicity,
                Expr::Lit(lit) if matches!(&lit.lit, syn::Lit::Int(int) if int.base10_digits() == "1")
            ) {
                left
            } else {
                syn::parse_quote!((#left) * (#multiplicity))
            };
            Ok((multiplicity, relation, values))
        }
        Expr::Paren(paren) => decompose_lookup_entry(*paren.expr),
        Expr::Group(group) => decompose_lookup_entry(*group.expr),
        other => Err(syn::Error::new_spanned(
            other,
            "lookup entries are written `multiplicity * relation(values, ...)`",
        )),
    }
}

/// The `lookups:` block of a table: LogUp entries in AIR/witness order plus
/// the finalization batch size (2 = pairs, the framework default; 1 for
/// tables whose quadratic denominators must stay in singleton batches).
pub(crate) struct LookupsDef {
    pub(crate) batch: usize,
    pub(crate) entries: Vec<LookupEntry>,
}

impl Default for LookupsDef {
    fn default() -> Self {
        LookupsDef {
            batch: 2,
            entries: Vec::new(),
        }
    }
}

fn parse_lookups(input: ParseStream) -> syn::Result<LookupsDef> {
    let mut lookups = LookupsDef::default();
    while !input.is_empty() {
        // `batch: N` is the only `key: value` item; entries are expressions.
        if input.peek(Ident) && input.peek2(Token![:]) {
            let key: Ident = input.parse()?;
            if key != "batch" {
                return Err(syn::Error::new(
                    key.span(),
                    "expected `batch: N` or a `multiplicity * relation(...)` entry",
                ));
            }
            input.parse::<Token![:]>()?;
            let lit: syn::LitInt = input.parse()?;
            lookups.batch = lit.base10_parse()?;
            if lookups.batch == 0 {
                return Err(syn::Error::new(lit.span(), "batch size must be positive"));
            }
        } else {
            let entry: Expr = input.parse()?;
            let (multiplicity, relation, values) = decompose_lookup_entry(entry)?;
            lookups.entries.push(LookupEntry {
                preprocessed: false,
                relation,
                multiplicity,
                values,
            });
        }
        if input.peek(Token![,]) {
            input.parse::<Token![,]>()?;
        }
    }
    Ok(lookups)
}

/// A single opcode definition:
/// `name: { committed: { field1, field2, ... }, derived: { ... }, constraints: { ... }, lookups: { ... } }`
///
/// Constraints are bare expressions with every trace column and derived
/// column in scope — like lookup entries, the formula itself names what it
/// reads, so a separate dependency list would be redundant.
pub(crate) struct OpcodeDef {
    pub(crate) name: Ident,
    pub(crate) fields: Vec<Ident>,
    pub(crate) derived: Vec<DerivedDef>,
    pub(crate) constraints: Vec<Expr>,
    pub(crate) lookups: LookupsDef,
    /// `air`-marked tables only define columns, constraints, and lookups —
    /// no `Tracer` field, table struct, or `trace_op!` arm (their traces are
    /// produced by custom runner code, e.g. the clock-update `AccessTable`).
    pub(crate) air_only: bool,
}

impl Parse for OpcodeDef {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut name: Ident = input.parse()?;
        let air_only = name == "air" && !input.peek(Token![:]);
        if air_only {
            name = input.parse()?;
        }
        input.parse::<Token![:]>()?;
        let content;
        braced!(content in input);

        let mut fields = Vec::new();
        let mut derived = Vec::new();
        let mut constraints = Vec::new();
        let mut lookups = LookupsDef::default();

        while !content.is_empty() {
            let ident: Ident = content.parse()?;
            if content.peek(Token![:]) {
                content.parse::<Token![:]>()?;
                let block;
                braced!(block in content);
                match ident.to_string().as_str() {
                    "committed" => {
                        if !fields.is_empty() {
                            return Err(syn::Error::new(
                                ident.span(),
                                "`committed` block may only be declared once",
                            ));
                        }
                        let defs: Punctuated<Ident, Token![,]> =
                            block.parse_terminated(Ident::parse, Token![,])?;
                        fields.extend(defs);
                    }
                    "derived" => {
                        let defs: Punctuated<DerivedDef, Token![,]> =
                            block.parse_terminated(DerivedDef::parse, Token![,])?;
                        derived.extend(defs);
                    }
                    "constraints" => {
                        let defs: Punctuated<Expr, Token![,]> =
                            block.parse_terminated(Expr::parse, Token![,])?;
                        constraints.extend(defs);
                    }
                    "lookups" => {
                        let parsed = block.call(parse_lookups)?;
                        lookups = parsed;
                    }
                    other => {
                        return Err(syn::Error::new(
                            ident.span(),
                            format!(
                                "unknown block `{other}`, expected `committed`, `derived`, `constraints`, or `lookups`"
                            ),
                        ));
                    }
                }
            } else {
                return Err(syn::Error::new(
                    ident.span(),
                    "trace columns must be declared inside `committed: { ... }`",
                ));
            }
            if content.peek(Token![,]) {
                content.parse::<Token![,]>()?;
            }
        }

        if fields.is_empty() {
            return Err(syn::Error::new(
                name.span(),
                "table must declare committed columns with `committed: { ... }`",
            ));
        }

        Ok(OpcodeDef {
            name,
            fields,
            derived,
            constraints,
            lookups,
            air_only,
        })
    }
}

/// All opcode definitions
pub(crate) struct TraceTablesDef {
    /// Relation names whose lookup entries register preprocessed multiplicities.
    preprocessed_relations: Vec<Ident>,
    pub(crate) opcodes: Vec<OpcodeDef>,
}

impl TraceTablesDef {
    /// Build a trace schema from opcode tables and preprocessed relation names.
    pub(crate) fn from_trace(opcodes: Vec<OpcodeDef>, preprocessed: &[RelationDef]) -> Self {
        let preprocessed_relations = preprocessed.iter().map(|rel| rel.name.clone()).collect();
        let mut def = Self {
            preprocessed_relations,
            opcodes,
        };
        def.apply_preprocessed_registry();
        def
    }

    /// Mark lookup entries whose relation name appears in the registry.
    fn apply_preprocessed_registry(&mut self) {
        let registered: std::collections::HashSet<String> = self
            .preprocessed_relations
            .iter()
            .map(|ident| ident.to_string())
            .collect();
        for opcode in &mut self.opcodes {
            for entry in &mut opcode.lookups.entries {
                if registered.contains(&entry.relation.to_string()) {
                    entry.preprocessed = true;
                }
            }
        }
    }
}

pub(crate) fn parse_opcode_defs(input: ParseStream) -> syn::Result<Vec<OpcodeDef>> {
    let opcodes: Punctuated<OpcodeDef, Token![,]> =
        input.parse_terminated(OpcodeDef::parse, Token![,])?;
    Ok(opcodes.into_iter().collect())
}

impl Parse for TraceTablesDef {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut preprocessed_relations = Vec::new();
        if input
            .cursor()
            .ident()
            .is_some_and(|(ident, _)| ident == "preprocessed_relations")
        {
            input.parse::<Ident>()?;
            input.parse::<Token![:]>()?;
            let content;
            braced!(content in input);
            let ids: Punctuated<Ident, Token![,]> =
                content.parse_terminated(Ident::parse, Token![,])?;
            preprocessed_relations.extend(ids);
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }
        }

        let opcodes = parse_opcode_defs(input)?;
        let mut def = TraceTablesDef {
            preprocessed_relations,
            opcodes,
        };
        def.apply_preprocessed_registry();
        Ok(def)
    }
}

/// Check if a field name represents an Access type (needs flattening)
fn is_access_field(name: &str) -> bool {
    matches!(name, "rd" | "rs1" | "rs2" | "mem" | "dst" | "src")
}

/// Check if a field name is an opcode flag (matches pattern `opcode_*_flag`)
fn is_opcode_flag(name: &str) -> bool {
    name.starts_with("opcode_") && name.ends_with("_flag")
}

/// Count the number of opcode flags in the fields list.
/// Used to determine whether to include an enabler column.
pub(crate) fn count_opcode_flags(fields: &[Ident]) -> usize {
    fields
        .iter()
        .filter(|f| is_opcode_flag(&f.to_string()))
        .count()
}

/// Convert a snake_case identifier to PascalCase.
/// E.g., "base_alu_imm" -> "BaseAluImm"
/// An external fn-DSL trace table folded into the `Tracer` (declared in the
/// `external:` section of `define_air!`). The table, columns, and component
/// are generated by `define_air_fns!` in `module`; the `Tracer` just holds a
/// field of the table type so the runner fills it like any opcode table.
pub(crate) struct ExternalTable {
    /// The `Tracer` field name (e.g. `poseidon2`).
    pub field: Ident,
    /// The module path the table lives in (e.g. `crate::poseidon2`).
    pub module: syn::Path,
}

impl ExternalTable {
    /// `<module>::<Pascal>Table`.
    pub(crate) fn table_type(&self) -> proc_macro2::TokenStream {
        let module = &self.module;
        let ty = format_ident!("{}Table", to_pascal_case(&self.field.to_string()));
        quote! { #module::#ty }
    }

    /// `<module>::prover_columns::<Pascal>Columns`.
    fn columns_type(&self) -> proc_macro2::TokenStream {
        let module = &self.module;
        let ty = format_ident!("{}Columns", to_pascal_case(&self.field.to_string()));
        quote! { #module::prover_columns::#ty }
    }
}

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

/// Generate the table struct name from opcode name (e.g., "base_alu_imm" -> "BaseAluImmTable")
pub(crate) fn table_name(opcode: &Ident) -> Ident {
    let pascal = to_pascal_case(&opcode.to_string());
    format_ident!("{}Table", pascal)
}

/// Generate columnar field declarations for a single field
fn generate_field_decls(field: &Ident) -> proc_macro2::TokenStream {
    let name = field.to_string();
    if is_access_field(&name) {
        // Access fields expand to 4 columns: addr, prev, clock_prev, next
        // Note: clock is NOT stored - it's redundant with tracer.clock at call site
        let addr = format_ident!("{}_addr", name);
        let prev = format_ident!("{}_prev", name);
        let clock_prev = format_ident!("{}_clock_prev", name);
        let next = format_ident!("{}_next", name);
        quote! {
            pub #addr: simd::AlignedVec<u32>,
            pub #prev: simd::AlignedVec<u32>,
            pub #clock_prev: simd::AlignedVec<u32>,
            pub #next: simd::AlignedVec<u32>,
        }
    } else {
        // Scalar field (clock, pc)
        quote! {
            pub #field: simd::AlignedVec<u32>,
        }
    }
}

/// Generate field initialization for new()
fn generate_field_init(field: &Ident) -> proc_macro2::TokenStream {
    let name = field.to_string();
    if is_access_field(&name) {
        // Access fields expand to 4 columns (no clock)
        let addr = format_ident!("{}_addr", name);
        let prev = format_ident!("{}_prev", name);
        let clock_prev = format_ident!("{}_clock_prev", name);
        let next = format_ident!("{}_next", name);
        quote! {
            #addr: simd::AlignedVec::new(),
            #prev: simd::AlignedVec::new(),
            #clock_prev: simd::AlignedVec::new(),
            #next: simd::AlignedVec::new(),
        }
    } else {
        quote! {
            #field: simd::AlignedVec::new(),
        }
    }
}

/// Generate field initialization with capacity
fn generate_field_init_cap(field: &Ident) -> proc_macro2::TokenStream {
    let name = field.to_string();
    if is_access_field(&name) {
        // Access fields expand to 4 columns (no clock)
        let addr = format_ident!("{}_addr", name);
        let prev = format_ident!("{}_prev", name);
        let clock_prev = format_ident!("{}_clock_prev", name);
        let next = format_ident!("{}_next", name);
        quote! {
            #addr: simd::AlignedVec::with_capacity(cap),
            #prev: simd::AlignedVec::with_capacity(cap),
            #clock_prev: simd::AlignedVec::with_capacity(cap),
            #next: simd::AlignedVec::with_capacity(cap),
        }
    } else {
        quote! {
            #field: simd::AlignedVec::with_capacity(cap),
        }
    }
}

/// Generate push method parameter for a field
fn generate_push_param(field: &Ident) -> proc_macro2::TokenStream {
    let name = field.to_string();
    if is_access_field(&name) {
        quote! { #field: Access }
    } else {
        quote! { #field: u32 }
    }
}

/// Generate push statements for a field
fn generate_push_stmt(field: &Ident) -> proc_macro2::TokenStream {
    let name = field.to_string();
    if is_access_field(&name) {
        // Access fields expand to 4 columns (no clock - it's available from tracer.clock)
        let addr = format_ident!("{}_addr", name);
        let prev = format_ident!("{}_prev", name);
        let clock_prev = format_ident!("{}_clock_prev", name);
        let next = format_ident!("{}_next", name);
        quote! {
            self.#addr.push(#field.addr);
            self.#prev.push(#field.prev);
            self.#clock_prev.push(#field.clock_prev);
            self.#next.push(#field.next);
        }
    } else {
        quote! {
            self.#field.push(#field);
        }
    }
}

/// Generate push-row statements for a field from a flat row slice
fn generate_push_row_stmt(field: &Ident) -> proc_macro2::TokenStream {
    let name = field.to_string();
    if is_access_field(&name) {
        // Access fields expand to 4 columns in trace order
        let addr = format_ident!("{}_addr", name);
        let prev = format_ident!("{}_prev", name);
        let clock_prev = format_ident!("{}_clock_prev", name);
        let next = format_ident!("{}_next", name);
        quote! {
            self.#addr.push(row[idx]);
            idx += 1;
            self.#prev.push(row[idx]);
            idx += 1;
            self.#clock_prev.push(row[idx]);
            idx += 1;
            self.#next.push(row[idx]);
            idx += 1;
        }
    } else {
        quote! {
            self.#field.push(row[idx]);
            idx += 1;
        }
    }
}

/// Generate debug field entries for a single row
fn generate_debug_field(field: &Ident) -> proc_macro2::TokenStream {
    let name = field.to_string();
    if is_access_field(&name) {
        // Access fields expand to 4 columns (no clock)
        let addr = format_ident!("{}_addr", name);
        let prev = format_ident!("{}_prev", name);
        let clock_prev = format_ident!("{}_clock_prev", name);
        let next = format_ident!("{}_next", name);
        let field_name = &name;
        quote! {
            .field(#field_name, &format_args!(
                "Access {{ addr: {:#x}, prev: {:#x}, clock_prev: {}, next: {:#x} }}",
                self.table.#addr[i],
                self.table.#prev[i],
                self.table.#clock_prev[i],
                self.table.#next[i]
            ))
        }
    } else {
        let field_name = &name;
        quote! {
            .field(#field_name, &self.table.#field[i])
        }
    }
}

/// Flatten field identifiers for prover columns.
/// Enabler is the first column only if `include_enabler` is true.
/// Access fields expand to 10 columns:
/// - addr (1 column)
/// - prev_0..prev_3 (4 limbs for u32 value)
/// - clock_prev (1 column)
/// - next_0..next_3 (4 limbs for u32 value)
fn flatten_fields(fields: &[Ident], include_enabler: bool) -> Vec<Ident> {
    let mut result = Vec::new();

    // Enabler is the first column only if no opcode flags are present
    if include_enabler {
        result.push(format_ident!("enabler"));
    }

    for field in fields {
        let name = field.to_string();
        if is_access_field(&name) {
            // Access fields expand to 10 columns with limbed prev/next
            result.push(format_ident!("{}_addr", name));
            // prev as 4 u8 limbs (little-endian)
            for i in 0usize..4 {
                result.push(format_ident!("{}_prev_{}", name, i));
            }
            result.push(format_ident!("{}_clock_prev", name));
            // next as 4 u8 limbs (little-endian)
            for i in 0usize..4 {
                result.push(format_ident!("{}_next_{}", name, i));
            }
        } else {
            result.push(field.clone());
        }
    }
    result
}

// =============================================================================
// Derived columns and constraints: expression compilation
// =============================================================================

/// How an identifier resolves inside a derived/constraint expression.
#[derive(Clone, Copy)]
enum ParamKind {
    /// A flattened trace column: rewritten to `self.name.clone()`.
    RawColumn,
    /// A derived column (or the synthesized `enabler`): rewritten to `self.name()`.
    Derived,
}

/// Emit a field constant `T::from(BaseField::from_u32_unchecked(value))`.
fn field_constant(value: &proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    quote! {
        T::from(stwo::core::fields::m31::BaseField::from_u32_unchecked(#value))
    }
}

/// The M31 prime, modulus of the base field.
pub(crate) const M31_PRIME: u64 = (1 << 31) - 1;

/// Modular exponentiation in M31, used to invert constants at expansion time.
pub(crate) fn m31_pow(mut base: u64, mut exp: u64) -> u64 {
    let mut result = 1u64;
    base %= M31_PRIME;
    while exp > 0 {
        if exp & 1 == 1 {
            result = result * base % M31_PRIME;
        }
        base = base * base % M31_PRIME;
        exp >>= 1;
    }
    result
}

/// Evaluate a constant integer sub-expression at expansion time: integer
/// literals, `pow2(n)`, parentheses, and `+`, `-`, `*`, `<<` thereof.
pub(crate) fn const_eval(expr: &Expr) -> syn::Result<u64> {
    let err = || {
        syn::Error::new_spanned(
            expr,
            "expected a constant integer expression (literals, pow2(n), +, -, *, <<)",
        )
    };
    match expr {
        Expr::Lit(lit) => match &lit.lit {
            syn::Lit::Int(int) => Ok(int.base10_parse::<u64>()? % M31_PRIME),
            _ => Err(err()),
        },
        Expr::Call(call) => {
            if let Expr::Path(func) = call.func.as_ref()
                && func.path.is_ident("pow2")
                && call.args.len() == 1
            {
                let exp = const_eval(&call.args[0])?;
                return Ok(m31_pow(2, exp));
            }
            Err(err())
        }
        Expr::Binary(bin) => {
            let left = const_eval(&bin.left)?;
            let right = const_eval(&bin.right)?;
            match bin.op {
                syn::BinOp::Add(_) => Ok((left + right) % M31_PRIME),
                syn::BinOp::Sub(_) => Ok((left + M31_PRIME - right) % M31_PRIME),
                syn::BinOp::Mul(_) => Ok(left * right % M31_PRIME),
                syn::BinOp::Shl(_) => Ok(m31_pow(2, right) * left % M31_PRIME),
                _ => Err(err()),
            }
        }
        Expr::Paren(paren) => const_eval(&paren.expr),
        Expr::Group(group) => const_eval(&group.expr),
        _ => Err(err()),
    }
}

/// Rewrite a derived/constraint expression into generic field arithmetic over `T`:
/// - column names become `self.col.clone()` (raw) or `self.col()` (derived)
/// - integer literals become `T::from(BaseField::from_u32_unchecked(lit))`
/// - `pow2(n)` becomes the constant `T::from(BaseField::from_u32_unchecked(1 << n))`
/// - `+`, `-`, `*`, unary `-`, and parentheses recurse
fn rewrite_expr(
    expr: &Expr,
    params: &HashMap<String, ParamKind>,
) -> syn::Result<proc_macro2::TokenStream> {
    // Any integer-only subtree (e.g. `(1 << 3) * ((1 << 5) - 1)`) folds to a
    // single field constant at expansion time.
    if let Ok(value) = const_eval(expr) {
        let value = value as u32;
        return Ok(field_constant(&quote! { #value }));
    }
    match expr {
        Expr::Path(p) => {
            if let Some(ident) = p.path.get_ident() {
                match params.get(&ident.to_string()) {
                    Some(ParamKind::RawColumn) => return Ok(quote! { self.#ident.clone() }),
                    Some(ParamKind::Derived) => return Ok(quote! { self.#ident() }),
                    None => {
                        return Err(syn::Error::new(
                            ident.span(),
                            format!(
                                "`{ident}` is not a trace column or previously defined derived column"
                            ),
                        ));
                    }
                }
            }
            Err(syn::Error::new_spanned(
                p,
                "only plain column identifiers are supported in derived expressions",
            ))
        }
        Expr::Lit(lit) => {
            if let syn::Lit::Int(int) = &lit.lit {
                let value = int.base10_parse::<u32>()?;
                Ok(field_constant(&quote! { #value }))
            } else {
                Err(syn::Error::new_spanned(
                    lit,
                    "only integer literals are supported in derived expressions",
                ))
            }
        }
        Expr::Call(call) => {
            // Intrinsics, all field constants resolved at expansion time:
            // - `pow2(n)`: 2^n
            // - `inv(c)`: multiplicative inverse of the constant expression `c`
            // - `constant(expr)`: an arbitrary `u32` const expression from the
            //   invocation site (e.g. `constant(crate::decode::Opcode::Addi as u32)`)
            if let Expr::Path(func) = call.func.as_ref() {
                if func.path.is_ident("pow2") && call.args.len() == 1 {
                    let value = m31_pow(2, const_eval(&call.args[0])?) as u32;
                    return Ok(field_constant(&quote! { #value }));
                }
                if func.path.is_ident("inv") && call.args.len() == 1 {
                    let value = const_eval(&call.args[0])?;
                    if value == 0 {
                        return Err(syn::Error::new_spanned(call, "cannot invert zero"));
                    }
                    let inverse = m31_pow(value, M31_PRIME - 2) as u32;
                    return Ok(field_constant(&quote! { #inverse }));
                }
                if func.path.is_ident("constant") && call.args.len() == 1 {
                    let arg = &call.args[0];
                    return Ok(field_constant(&quote! { (#arg) }));
                }
            }
            Err(syn::Error::new_spanned(
                call,
                "only the pow2(n), inv(c), and constant(expr) intrinsics are callable in derived expressions",
            ))
        }
        Expr::Binary(bin) => {
            let op = &bin.op;
            match op {
                syn::BinOp::Add(_) | syn::BinOp::Sub(_) | syn::BinOp::Mul(_) => {
                    let left = rewrite_expr(&bin.left, params)?;
                    let right = rewrite_expr(&bin.right, params)?;
                    Ok(quote! { (#left #op #right) })
                }
                _ => Err(syn::Error::new_spanned(
                    bin,
                    "only +, -, * are supported in derived expressions",
                )),
            }
        }
        Expr::Unary(unary) => {
            if matches!(unary.op, syn::UnOp::Neg(_)) {
                let inner = rewrite_expr(&unary.expr, params)?;
                Ok(quote! { (-#inner) })
            } else {
                Err(syn::Error::new_spanned(
                    unary,
                    "only unary minus is supported in derived expressions",
                ))
            }
        }
        Expr::Paren(paren) => rewrite_expr(&paren.expr, params),
        Expr::Group(group) => rewrite_expr(&group.expr, params),
        other => Err(syn::Error::new_spanned(
            other,
            "unsupported expression in derived column or constraint",
        )),
    }
}

/// The full expression scope of a table: every flattened trace column and
/// every derived column (including the synthesized `enabler`).
fn full_scope(flat_columns: &[Ident], derived_names: &[Ident]) -> HashMap<String, ParamKind> {
    let mut scope = HashMap::new();
    for column in flat_columns {
        scope.insert(column.to_string(), ParamKind::RawColumn);
    }
    for derived in derived_names {
        scope.insert(derived.to_string(), ParamKind::Derived);
    }
    scope
}

/// Compile an expression into a generic expression body over `T`.
fn compile_expr(
    expr: &Expr,
    flat_columns: &[Ident],
    derived_names: &[Ident],
) -> syn::Result<proc_macro2::TokenStream> {
    let scope = full_scope(flat_columns, derived_names);
    rewrite_expr(expr, &scope)
}

/// Count trace columns (enabler + fields, with Access fields expanding to 4 columns).
fn trace_columns_len(fields: &[Ident], include_enabler: bool) -> usize {
    let mut count = if include_enabler { 1 } else { 0 };
    for field in fields {
        let name = field.to_string();
        if is_access_field(&name) {
            count += 4;
        } else {
            count += 1;
        }
    }
    count
}

/// Generate the into_columns body that splits u32 values into limbs.
/// This handles the conversion from the trace table's u32 storage to
/// the prover's limbed representation.
/// Enabler is the first column only if `include_enabler` is true.
fn generate_into_columns_body(fields: &[Ident], include_enabler: bool) -> proc_macro2::TokenStream {
    let mut column_exprs = Vec::new();

    // Enabler is the first column only if no opcode flags are present
    if include_enabler {
        column_exprs.push(quote! { self.enabler });
    }

    for field in fields {
        let name = field.to_string();
        if is_access_field(&name) {
            let addr = format_ident!("{}_addr", name);
            let prev = format_ident!("{}_prev", name);
            let clock_prev = format_ident!("{}_clock_prev", name);
            let next = format_ident!("{}_next", name);

            // addr column
            column_exprs.push(quote! { self.#addr });

            // prev as 4 limbs (little-endian: limb 0 is least significant byte)
            for i in 0u8..4 {
                let shift = i * 8;
                column_exprs.push(quote! {
                    {
                        let mut v = simd::AlignedVec::with_capacity(self.#prev.len());
                        for val in self.#prev.iter() {
                            v.push(((val >> #shift) & 0xFF) as u32);
                        }
                        v
                    }
                });
            }

            // clock_prev column
            column_exprs.push(quote! { self.#clock_prev });

            // next as 4 limbs (little-endian: limb 0 is least significant byte)
            for i in 0u8..4 {
                let shift = i * 8;
                column_exprs.push(quote! {
                    {
                        let mut v = simd::AlignedVec::with_capacity(self.#next.len());
                        for val in self.#next.iter() {
                            v.push(((val >> #shift) & 0xFF) as u32);
                        }
                        v
                    }
                });
            }
        } else {
            // Scalar field (clock, pc) - return directly
            column_exprs.push(quote! { self.#field });
        }
    }

    quote! {
        vec![
            #(#column_exprs),*
        ]
    }
}

/// Generate column struct name (e.g., "base_alu_imm" -> "BaseAluImmColumns")
pub(crate) fn column_struct_name(opcode: &Ident) -> Ident {
    let pascal = to_pascal_case(&opcode.to_string());
    format_ident!("{}Columns", pascal)
}

/// Generate Table column entries for a table (used by to_table method).
/// Returns tuples of (column_name_str, field_access_expr) for slices_to_table.
fn generate_table_columns(
    fields: &[Ident],
    include_enabler: bool,
) -> Vec<proc_macro2::TokenStream> {
    let mut columns = Vec::new();

    // Enabler first if present
    if include_enabler {
        columns.push(quote! { ("enabler", &self.enabler[..]) });
    }

    for field in fields {
        let name = field.to_string();
        if is_access_field(&name) {
            // Access fields have 4 columns: addr, prev, clock_prev, next
            let addr = format_ident!("{}_addr", name);
            let prev = format_ident!("{}_prev", name);
            let clock_prev = format_ident!("{}_clock_prev", name);
            let next = format_ident!("{}_next", name);

            let addr_name = format!("{name}_addr");
            let prev_name = format!("{name}_prev");
            let clock_prev_name = format!("{name}_clock_prev");
            let next_name = format!("{name}_next");

            columns.push(quote! { (#addr_name, &self.#addr[..]) });
            columns.push(quote! { (#prev_name, &self.#prev[..]) });
            columns.push(quote! { (#clock_prev_name, &self.#clock_prev[..]) });
            columns.push(quote! { (#next_name, &self.#next[..]) });
        } else {
            // Scalar field
            let field_name = name.clone();
            columns.push(quote! { (#field_name, &self.#field[..]) });
        }
    }

    columns
}

/// Generate the generic expression impl: derived column methods, the
/// synthesized `enabler()` for flag tables, and `constraints()`.
///
/// The impl is generic over `T` with field-arithmetic bounds satisfied both by
/// `E::F` (symbolic AIR evaluation) and `PackedM31` (SIMD witness generation),
/// so each expression is written once and used in both worlds.
fn generate_expr_impl(
    opcode: &OpcodeDef,
    struct_name: &Ident,
    flat_fields: &[Ident],
    include_enabler: bool,
) -> syn::Result<proc_macro2::TokenStream> {
    let opcode_flags: Vec<Ident> = opcode
        .fields
        .iter()
        .filter(|f| is_opcode_flag(&f.to_string()))
        .cloned()
        .collect();

    // Flag tables get a synthesized `enabler()` (sum of flags) unless the user
    // defines their own derived `enabler`.
    let user_defines_enabler = opcode.derived.iter().any(|d| d.name == "enabler");
    let synthesize_enabler = !include_enabler && !user_defines_enabler;

    let mut derived_names: Vec<Ident> = Vec::new();
    if synthesize_enabler {
        derived_names.push(format_ident!("enabler"));
    }

    let mut methods: Vec<proc_macro2::TokenStream> = Vec::new();

    if synthesize_enabler {
        let sum = opcode_flags
            .iter()
            .map(|f| quote! { self.#f.clone() })
            .reduce(|acc, f| quote! { (#acc + #f) })
            .expect("flag tables have at least one opcode flag");
        methods.push(quote! {
            /// Row activity indicator: sum of the opcode flags.
            #[inline(always)]
            pub fn enabler(&self) -> T {
                #sum
            }
        });
    }

    for def in &opcode.derived {
        if flat_fields.contains(&def.name) {
            return Err(syn::Error::new(
                def.name.span(),
                format!("derived column `{}` collides with a trace column", def.name),
            ));
        }
        let body = compile_expr(&def.expr, flat_fields, &derived_names)?;
        let name = &def.name;
        let expr = &def.expr;
        let doc = format!("Derived column: `{}`.", quote!(#expr));
        methods.push(quote! {
            #[doc = #doc]
            #[inline(always)]
            pub fn #name(&self) -> T {
                #body
            }
        });
        derived_names.push(def.name.clone());
    }

    // Booleanity is structural: the enabler (and each opcode flag) is 0 or 1.
    // These constraints are always emitted so components don't repeat them.
    let one = field_constant(&quote! { 1u32 });
    let mut constraint_exprs: Vec<proc_macro2::TokenStream> = Vec::new();
    let enabler_access = if include_enabler {
        quote! { self.enabler.clone() }
    } else {
        quote! { self.enabler() }
    };
    constraint_exprs.push(quote! {
        {
            let e = #enabler_access;
            e.clone() * (#one - e)
        }
    });
    for flag in &opcode_flags {
        constraint_exprs.push(quote! {
            {
                let f = self.#flag.clone();
                f.clone() * (#one - f)
            }
        });
    }
    let scope = full_scope(flat_fields, &derived_names);
    for constraint in &opcode.constraints {
        constraint_exprs.push(rewrite_expr(constraint, &scope)?);
    }

    // Lookup entries: multiplicity and tuple expressions over the full column
    // scope (every trace column and derived column — the tuple itself lists
    // what the entry reads, so no separate dependency list is needed).
    let lookup_method = if opcode.lookups.entries.is_empty() {
        quote! {}
    } else {
        let mut entry_exprs: Vec<proc_macro2::TokenStream> = Vec::new();
        for entry in &opcode.lookups.entries {
            let multiplicity = rewrite_expr(&entry.multiplicity, &scope)?;
            let values = entry
                .values
                .iter()
                .map(|value| rewrite_expr(value, &scope))
                .collect::<syn::Result<Vec<_>>>()?;
            entry_exprs.push(quote! {
                (#multiplicity, vec![#(#values),*])
            });
        }
        quote! {
            /// LogUp lookup entries declared in `define_trace_tables!`:
            /// `(multiplicity, tuple values)` in declaration order — the
            /// single source for the AIR relation entries, the interaction
            /// trace, and the preprocessed multiplicity registration.
            pub fn lookup_entries(&self) -> Vec<(T, Vec<T>)> {
                vec![
                    #(#entry_exprs),*
                ]
            }
        }
    };

    Ok(quote! {
        impl<T> #struct_name<T>
        where
            T: Clone
                + From<stwo::core::fields::m31::BaseField>
                + core::ops::Add<Output = T>
                + core::ops::Sub<Output = T>
                + core::ops::Mul<Output = T>
                + core::ops::Neg<Output = T>,
        {
            #(#methods)*

            /// Constraint expressions; each must evaluate to zero on every row.
            ///
            /// Includes booleanity of the enabler and opcode flags, followed by
            /// the constraints declared in `define_trace_tables!`.
            pub fn constraints(&self) -> Vec<T> {
                vec![
                    #(#constraint_exprs),*
                ]
            }

            #lookup_method
        }
    })
}

/// Generate the three exported lookup macros of a table with a `lookups:`
/// block:
/// - `<table>_lookups!(eval, cols, relations)` — the AIR side: one
///   `add_to_relation` per entry plus the batched LogUp finalization.
/// - `<table>_interaction!(trace, relations)` — the witness side: the full
///   interaction-trace generation, entries paired exactly as the AIR
///   finalization batches them; evaluates to `(columns, claimed_sum)`.
/// - `<table>_register_multiplicities!(trace, counters)` — registers the
///   consumption multiplicities of every `preprocessed`-marked entry.
///
/// The macros bake the relation field names; the `relations`/`counters`
/// arguments are the structs holding those fields, so the relation
/// definitions stay in the `relations!` invocation. The column struct ident
/// resolves at the call site (callers import it alongside the macro).
pub(crate) fn generate_lookup_macros(
    opcode: &OpcodeDef,
    include_enabler: bool,
) -> proc_macro2::TokenStream {
    if opcode.lookups.entries.is_empty() {
        return quote! {};
    }
    let columns_struct = column_struct_name(&opcode.name);
    let lookups_macro = format_ident!("{}_lookups", opcode.name);
    let dynamic_lookups_macro = format_ident!("{}_dynamic_lookups", opcode.name);
    let interaction_macro = format_ident!("{}_interaction", opcode.name);
    let register_macro = format_ident!("{}_register_multiplicities", opcode.name);
    let batch = opcode.lookups.batch;
    let n_entries = opcode.lookups.entries.len();

    // First flattened column, used for the SIMD length.
    let first_column = if include_enabler {
        format_ident!("enabler")
    } else {
        let first = &opcode.fields[0];
        if is_access_field(&first.to_string()) {
            format_ident!("{}_addr", first)
        } else {
            first.clone()
        }
    };

    // AIR side: relation entries in declaration order, then finalization.
    let air_entries: Vec<_> = opcode
        .lookups
        .entries
        .iter()
        .map(|entry| {
            let relation = &entry.relation;
            quote! {
                {
                    let (multiplicity, values) = entries.next().expect("lookup entry");
                    $eval.add_to_relation(stwo_constraint_framework::RelationEntry::new(
                        &$relations.#relation,
                        multiplicity.into(),
                        &values,
                    ));
                }
            }
        })
        .collect();
    let dynamic_air_entries: Vec<_> = opcode
        .lookups
        .entries
        .iter()
        .map(|entry| {
            let relation = &entry.relation;
            quote! {
                {
                    let (multiplicity, values) = entries.next().expect("lookup entry");
                    $eval.add_to_named_relation(
                        stringify!(#relation),
                        multiplicity.into(),
                        &values,
                    );
                }
            }
        })
        .collect();
    let finalize = if batch == 2 {
        quote! { $eval.finalize_logup_in_pairs(); }
    } else if batch == 1 {
        quote! { $eval.finalize_logup(); }
    } else {
        // Per-fraction batch assignments, computed at expansion time.
        let assignments: Vec<usize> = (0..n_entries).map(|entry| entry / batch).collect();
        quote! { $eval.finalize_logup_batched(&vec![#(#assignments),*]); }
    };

    // Witness side: per-row entry evaluation through the same
    // `lookup_entries()` (via `at(i)`), then fraction columns batched exactly
    // as the AIR finalization pairs them.
    let witness_entry_stmts: Vec<_> = opcode
        .lookups
        .entries
        .iter()
        .enumerate()
        .map(|(index, entry)| {
            let relation = &entry.relation;
            quote! {
                {
                    let (multiplicity, values) = &entries[#index];
                    numerators[#index].push(
                        stwo::prover::backend::simd::qm31::PackedQM31::from(*multiplicity),
                    );
                    denominators[#index].push(stwo_constraint_framework::Relation::combine(
                        &$relations.#relation,
                        values,
                    ));
                }
            }
        })
        .collect();
    let mut write_stmts: Vec<proc_macro2::TokenStream> = Vec::new();
    let mut index = 0usize;
    while index < n_entries {
        if batch >= 2 && index + 1 < n_entries {
            let (first, second) = (index, index + 1);
            write_stmts.push(quote! {
                {
                    let mut col = logup_gen.new_col();
                    for (vec_row, (((n0, d0), n1), d1)) in numerators[#first]
                        .iter()
                        .zip(denominators[#first].iter())
                        .zip(numerators[#second].iter())
                        .zip(denominators[#second].iter())
                        .enumerate()
                    {
                        col.write_frac(vec_row, *n0 * *d1 + *n1 * *d0, *d0 * *d1);
                    }
                    col.finalize_col();
                }
            });
            index += 2;
        } else {
            write_stmts.push(quote! {
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
            });
            index += 1;
        }
    }

    // Preprocessed multiplicity registration for the marked entries.
    let marked: Vec<(usize, &LookupEntry)> = opcode
        .lookups
        .entries
        .iter()
        .enumerate()
        .filter(|(_, entry)| entry.preprocessed)
        .collect();
    let register_body = if marked.is_empty() {
        quote! {
            let _ = $trace;
            let _ = $counters;
        }
    } else {
        let collect_stmts: Vec<_> = marked
            .iter()
            .enumerate()
            .map(|(slot, (entry_index, entry))| {
                let n_values = entry.values.len();
                quote! {
                    {
                        let (multiplicity, values) = &entries[#entry_index];
                        multiplicities[#slot].push(*multiplicity);
                        debug_assert_eq!(values.len(), #n_values);
                        for (element, value) in elements[#slot].iter_mut().zip(values.iter()) {
                            element.push(*value);
                        }
                    }
                }
            })
            .collect();
        let element_inits: Vec<_> = marked
            .iter()
            .map(|(_, entry)| {
                let n_values = entry.values.len();
                quote! { vec![Vec::with_capacity(simd_size); #n_values] }
            })
            .collect();
        let register_stmts: Vec<_> = marked
            .iter()
            .enumerate()
            .map(|(slot, (_, entry))| {
                let relation = &entry.relation;
                quote! {
                    $counters.#relation.register_many(
                        &multiplicities[#slot],
                        &elements[#slot]
                            .iter()
                            .map(|column| column.as_slice())
                            .collect::<Vec<_>>(),
                    );
                }
            })
            .collect();
        let n_marked = marked.len();
        quote! {
            let cols = #columns_struct::from_iter($trace.iter().map(|eval| &eval.values.data));
            let simd_size = cols.#first_column.len();
            let mut multiplicities: Vec<Vec<stwo::prover::backend::simd::m31::PackedM31>> =
                vec![Vec::with_capacity(simd_size); #n_marked];
            let mut elements: Vec<Vec<Vec<stwo::prover::backend::simd::m31::PackedM31>>> =
                vec![#(#element_inits),*];
            for i in 0..simd_size {
                let entries = cols.at(i).lookup_entries();
                #(#collect_stmts)*
            }
            #(#register_stmts)*
        }
    };

    quote! {
        #[macro_export]
        macro_rules! #lookups_macro {
            ($eval:expr, $cols:expr, $relations:expr) => {{
                let mut entries = $cols.lookup_entries().into_iter();
                #(#air_entries)*
                #finalize
            }};
        }

        #[macro_export]
        macro_rules! #dynamic_lookups_macro {
            ($eval:expr, $cols:expr) => {{
                let mut entries = $cols.lookup_entries().into_iter();
                #(#dynamic_air_entries)*
                #finalize
            }};
        }

        #[macro_export]
        macro_rules! #interaction_macro {
            ($trace:expr, $relations:expr) => {{
                let cols = #columns_struct::from_iter($trace.iter().map(|eval| &eval.values.data));
                let simd_size = cols.#first_column.len();
                let log_size = $trace[0].domain.log_size();
                let mut logup_gen = stwo_constraint_framework::LogupTraceGenerator::new(log_size);
                let mut numerators: Vec<Vec<stwo::prover::backend::simd::qm31::PackedQM31>> =
                    vec![Vec::with_capacity(simd_size); #n_entries];
                let mut denominators: Vec<Vec<stwo::prover::backend::simd::qm31::PackedQM31>> =
                    vec![Vec::with_capacity(simd_size); #n_entries];
                for i in 0..simd_size {
                    let entries = cols.at(i).lookup_entries();
                    #(#witness_entry_stmts)*
                }
                #(#write_stmts)*
                logup_gen.finalize_last()
            }};
        }

        #[macro_export]
        macro_rules! #register_macro {
            ($trace:expr, $counters:expr) => {{
                #register_body
            }};
        }
    }
}

/// Generate the `at(i)` row extractor: turns a columns-of-vectors view (as
/// built by `from_iter` over the witness trace) into a single row of scalars,
/// so derived columns and constraints evaluate per SIMD row.
fn generate_at_impl(struct_name: &Ident, flat_fields: &[Ident]) -> proc_macro2::TokenStream {
    let field_extracts: Vec<_> = flat_fields
        .iter()
        .map(|f| quote! { #f: self.#f[i] })
        .collect();
    quote! {
        impl<'a, T: Copy> #struct_name<&'a Vec<T>> {
            /// Extract row `i` as scalar values.
            #[inline(always)]
            pub fn at(&self, i: usize) -> #struct_name<T> {
                #struct_name {
                    #(#field_extracts),*
                }
            }
        }
    }
}

/// Generate prover column struct for AIR evaluation
pub(crate) fn generate_prover_columns(opcode: &OpcodeDef) -> syn::Result<proc_macro2::TokenStream> {
    let struct_name = column_struct_name(&opcode.name);
    // Include enabler only if no opcode flags are present
    let include_enabler = count_opcode_flags(&opcode.fields) == 0;
    let flat_fields = flatten_fields(&opcode.fields, include_enabler);
    let field_count = flat_fields.len();

    let owned_fields: Vec<_> = flat_fields.iter().map(|f| quote! { pub #f: T }).collect();

    // Generate field names as strings for NAMES constant
    let field_names: Vec<String> = flat_fields.iter().map(|f| f.to_string()).collect();

    let from_eval_fields: Vec<_> = flat_fields
        .iter()
        .map(|f| quote! { #f: eval.next_trace_mask() })
        .collect();

    let from_iter_fields: Vec<_> = flat_fields
        .iter()
        .map(|f| {
            let field_name = f.to_string();
            quote! { #f: iter.next().expect(concat!("not enough columns for field: ", #field_name)) }
        })
        .collect();

    let expr_impl = generate_expr_impl(opcode, &struct_name, &flat_fields, include_enabler)?;
    let at_impl = generate_at_impl(&struct_name, &flat_fields);

    Ok(quote! {
        /// Column struct for AIR evaluation.
        #[derive(Debug, Clone)]
        pub struct #struct_name<T> {
            #(#owned_fields),*
        }

        impl<T> #struct_name<T> {
            /// Number of columns in this struct.
            pub const SIZE: usize = #field_count;

            /// Column names as strings (for debug printing).
            pub const NAMES: &'static [&'static str] = &[
                #(#field_names),*
            ];

            /// Construct from an AIR evaluator by reading trace masks.
            #[inline(always)]
            pub fn from_eval<E>(eval: &mut E) -> Self
            where E: EvalAtRow<F = T>
            {
                Self {
                    #(#from_eval_fields),*
                }
            }

            /// Construct from an iterator of column values.
            /// Panics if iterator has fewer elements than the number of columns.
            #[inline(always)]
            pub fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
                let mut iter = iter.into_iter();
                Self {
                    #(#from_iter_fields),*
                }
            }
        }

        #expr_impl

        #at_impl
    })
}

/// Generate a single table struct and impl
pub(crate) fn generate_table(opcode: &OpcodeDef) -> proc_macro2::TokenStream {
    let struct_name = table_name(&opcode.name);

    // Determine if we should include enabler based on opcode flags
    let include_enabler = count_opcode_flags(&opcode.fields) == 0;

    let field_decls: Vec<_> = opcode.fields.iter().map(generate_field_decls).collect();
    let field_inits: Vec<_> = opcode.fields.iter().map(generate_field_init).collect();
    let field_inits_cap: Vec<_> = opcode.fields.iter().map(generate_field_init_cap).collect();
    let push_params: Vec<_> = opcode.fields.iter().map(generate_push_param).collect();
    let push_stmts: Vec<_> = opcode.fields.iter().map(generate_push_stmt).collect();
    let push_row_stmts: Vec<_> = opcode.fields.iter().map(generate_push_row_stmt).collect();
    let debug_fields: Vec<_> = opcode.fields.iter().map(generate_debug_field).collect();

    // Generate into_columns body that splits u32 values into limbs
    let into_columns_body = generate_into_columns_body(&opcode.fields, include_enabler);
    let row_len = trace_columns_len(&opcode.fields, include_enabler);

    // Get the first field name for len/is_empty when no enabler
    // We need to find the first actual column name after expansion
    let first_field = &opcode.fields[0];
    let first_field_name = first_field.to_string();
    let len_field = if is_access_field(&first_field_name) {
        format_ident!("{}_addr", first_field_name)
    } else {
        first_field.clone()
    };

    // Conditional enabler components
    let enabler_field_decl = if include_enabler {
        quote! {
            /// Enabler column: 1 for real rows, 0 for padding.
            pub enabler: simd::AlignedVec<u32>,
        }
    } else {
        quote! {}
    };

    let enabler_field_init = if include_enabler {
        quote! { enabler: simd::AlignedVec::new(), }
    } else {
        quote! {}
    };

    let enabler_field_init_cap = if include_enabler {
        quote! { enabler: simd::AlignedVec::with_capacity(cap), }
    } else {
        quote! {}
    };

    let enabler_push_stmt = if include_enabler {
        quote! { self.enabler.push(1); }
    } else {
        quote! {}
    };

    let enabler_push_row_stmt = if include_enabler {
        quote! {
            self.enabler.push(row[idx]);
            idx += 1;
        }
    } else {
        quote! {}
    };

    let enabler_debug_field = if include_enabler {
        quote! { .field("enabler", &self.table.enabler[i]) }
    } else {
        quote! {}
    };

    let len_impl = if include_enabler {
        quote! { self.enabler.len() }
    } else {
        quote! { self.#len_field.len() }
    };

    let is_empty_impl = if include_enabler {
        quote! { self.enabler.is_empty() }
    } else {
        quote! { self.#len_field.is_empty() }
    };

    let into_columns_doc = if include_enabler {
        "Enabler is the first column, followed by other fields."
    } else {
        "No enabler column (deduced from opcode flags in AIR)."
    };

    // Generate Table column entries for to_table method
    let table_columns = generate_table_columns(&opcode.fields, include_enabler);

    quote! {
        #[derive(Clone, Default)]
        pub struct #struct_name {
            #enabler_field_decl
            #(#field_decls)*
        }

        impl std::fmt::Debug for #struct_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let mut list = f.debug_list();
                for i in 0..self.len() {
                    // Create a debug struct for each row
                    struct Row<'a> {
                        table: &'a #struct_name,
                        idx: usize,
                    }
                    impl std::fmt::Debug for Row<'_> {
                        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                            let i = self.idx;
                            f.debug_struct("")
                                #enabler_debug_field
                                #(#debug_fields)*
                                .finish()
                        }
                    }
                    list.entry(&Row { table: self, idx: i });
                }
                list.finish()
            }
        }

        impl #struct_name {
            pub fn new() -> Self {
                Self {
                    #enabler_field_init
                    #(#field_inits)*
                }
            }

            pub fn with_capacity(cap: usize) -> Self {
                Self {
                    #enabler_field_init_cap
                    #(#field_inits_cap)*
                }
            }

            #[inline]
            pub fn len(&self) -> usize {
                #len_impl
            }

            #[inline]
            pub fn is_empty(&self) -> bool {
                #is_empty_impl
            }

            #[inline]
            #[allow(clippy::too_many_arguments)]
            pub fn push(&mut self, #(#push_params),*) {
                #enabler_push_stmt
                #(#push_stmts)*
            }

            #[inline]
            pub fn push_row(&mut self, row: &[u32]) {
                debug_assert_eq!(row.len(), #row_len);
                let mut idx = 0usize;
                #enabler_push_row_stmt
                #(#push_row_stmts)*
            }

            /// Consumes the table and returns columns as a Vec in canonical order.
            /// Order matches the column struct field order.
            #[doc = #into_columns_doc]
            /// Access fields have prev/next split into 4 u8 limbs (little-endian).
            pub fn into_columns(self) -> Vec<simd::AlignedVec<u32>> {
                #into_columns_body
            }

            /// Convert table to trace columns, padding to power of 2.
            /// Always produces columns with minimum log_size of 4 (16 rows),
            /// even for empty tables.
            ///
            /// Consumes self since the table is no longer needed after trace generation.
            pub fn into_witness(
                self,
            ) -> Vec<stwo::prover::poly::circle::CircleEvaluation<
                stwo::prover::backend::simd::SimdBackend,
                stwo::core::fields::m31::BaseField,
                stwo::prover::poly::BitReversedOrder,
            >> {
                use stwo::core::poly::circle::CanonicCoset;
                use stwo::prover::backend::simd::column::BaseColumn;
                use stwo::prover::poly::circle::CircleEvaluation;

                let len = self.len() as u32;
                let log_size = len.next_power_of_two().ilog2().max(4);
                let padded_len = 1 << log_size;
                let columns = self.into_columns();
                let domain = CanonicCoset::new(log_size).circle_domain();

                columns
                    .into_iter()
                    .map(|mut col| {
                        col.resize(padded_len as usize, 0);
                        let base_col: BaseColumn = col.into();
                        CircleEvaluation::new(domain, base_col)
                    })
                    .collect()
            }

            /// Convert this table to a formatted Table for debugging.
            pub fn to_table(&self) -> debug_utils::Table {
                debug_utils::slices_to_table(&[
                    #(#table_columns),*
                ])
            }
        }
    }
}

/// Generate the Tracer struct
fn generate_tracer(
    opcodes: &[&OpcodeDef],
    externals: &[ExternalTable],
    access_table: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    // External fn-DSL tables: a `Tracer` field per declared table, generated
    // from the `external:` section instead of hardcoded.
    let external_fields: Vec<_> = externals
        .iter()
        .map(|ext| {
            let field = &ext.field;
            let ty = ext.table_type();
            quote! { pub #field: #ty }
        })
        .collect();
    let external_inits: Vec<_> = externals
        .iter()
        .map(|ext| {
            let field = &ext.field;
            let ty = ext.table_type();
            quote! { #field: #ty::new() }
        })
        .collect();
    let external_total_traces: Vec<_> = externals
        .iter()
        .map(|ext| {
            let field = &ext.field;
            quote! { + self.#field.len() }
        })
        .collect();
    let external_debug_fields: Vec<_> = externals
        .iter()
        .map(|ext| {
            let field = &ext.field;
            let field_str = field.to_string();
            quote! { .field(#field_str, &self.#field) }
        })
        .collect();

    let table_fields: Vec<_> = opcodes
        .iter()
        .map(|op| {
            let name = &op.name;
            let ty = table_name(name);
            quote! { pub #name: #ty }
        })
        .collect();

    let table_inits: Vec<_> = opcodes
        .iter()
        .map(|op| {
            let name = &op.name;
            let ty = table_name(name);
            quote! { #name: #ty::new() }
        })
        .collect();

    let table_inits_cap: Vec<_> = opcodes
        .iter()
        .map(|op| {
            let name = &op.name;
            let ty = table_name(name);
            quote! { #name: #ty::with_capacity(cap) }
        })
        .collect();

    let total_traces_sum: Vec<_> = opcodes
        .iter()
        .map(|op| {
            let name = &op.name;
            quote! { + self.#name.len() }
        })
        .collect();

    // Per-table row counts for the segment-capacity check: a segment closes
    // when the largest table would overflow its budget, not after a fixed
    // cycle count.
    let external_max_updates: Vec<_> = externals
        .iter()
        .map(|ext| {
            let field = &ext.field;
            quote! { m = m.max(self.#field.len()); }
        })
        .collect();
    let opcode_max_updates: Vec<_> = opcodes
        .iter()
        .map(|op| {
            let name = &op.name;
            quote! { m = m.max(self.#name.len()); }
        })
        .collect();

    let debug_table_fields: Vec<_> = opcodes
        .iter()
        .map(|op| {
            let name = &op.name;
            let name_str = name.to_string();
            quote! { .field(#name_str, &self.#name) }
        })
        .collect();

    let print_table_stmts: Vec<_> = opcodes
        .iter()
        .map(|op| {
            let name = &op.name;
            let name_str = name.to_string();
            quote! {
                if !self.#name.is_empty() {
                    println!("\n=== {} ({} rows) ===", #name_str, self.#name.len());
                    println!("{}", self.#name.to_table());
                }
            }
        })
        .collect();

    quote! {
        /// Main tracer structure holding all per-opcode columnar trace tables.
        pub struct Tracer {
            /// Global clock counter, incremented by 1 at each instruction.
            pub clock: u32,
            /// Maximum allowed clock difference between consecutive accesses.
            pub max_clock_diff: u32,

            /// Last access clock for each register (0-31).
            pub reg_clock: [u32; 32],
            /// Last access clock for each memory address.
            pub mem_clock: rustc_hash::FxHashMap<u32, u32>,
            /// Value at first access for each memory word (4-byte aligned address).
            pub mem_initial: rustc_hash::FxHashMap<u32, u32>,
            /// Program fetch counts per PC.
            pub program_reads: rustc_hash::FxHashMap<u32, u32>,

            /// Synthetic clock catch-up rows for register and memory accesses.
            pub clock_update: #access_table,

            // External fn-DSL tables (felt-generated, e.g. `poseidon2`).
            #(#external_fields,)*

            // Per-opcode trace tables
            #(#table_fields,)*
        }

        impl std::fmt::Debug for Tracer {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                // Wrapper to display u32 in hex
                struct Hex(u32);
                impl std::fmt::Debug for Hex {
                    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        write!(f, "{:#x}", self.0)
                    }
                }

                // Wrapper to display HashMap keys in hex
                struct HexKeyMap<'a>(&'a rustc_hash::FxHashMap<u32, u32>);
                impl std::fmt::Debug for HexKeyMap<'_> {
                    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        f.debug_map()
                            .entries(self.0.iter().map(|(k, v)| (Hex(*k), v)))
                            .finish()
                    }
                }

                f.debug_struct("Tracer")
                    .field("clock", &self.clock)
                    .field("max_clock_diff", &self.max_clock_diff)
                    .field("reg_clock", &self.reg_clock)
                    .field("mem_clock", &HexKeyMap(&self.mem_clock))
                    .field("mem_initial", &HexKeyMap(&self.mem_initial))
                    .field("program_reads", &HexKeyMap(&self.program_reads))
                    .field("clock_update", &self.clock_update)
                    #(#external_debug_fields)*
                    #(#debug_table_fields)*
                    .finish()
            }
        }

        impl Default for Tracer {
            fn default() -> Self {
                Self {
                    clock: 0,
                    max_clock_diff: DEFAULT_MAX_CLOCK_DIFF,
                    reg_clock: [0; 32],
                    mem_clock: rustc_hash::FxHashMap::default(),
                    mem_initial: rustc_hash::FxHashMap::default(),
                    program_reads: rustc_hash::FxHashMap::default(),
                    clock_update: #access_table::new(),
                    #(#external_inits,)*
                    #(#table_inits,)*
                }
            }
        }

        impl Tracer {
            /// Create a new tracer with custom max clock diff.
            pub fn with_max_clock_diff(max_clock_diff: u32) -> Self {
                Self {
                    max_clock_diff,
                    clock_update: #access_table::with_max_clock_diff(max_clock_diff),
                    ..Default::default()
                }
            }

            /// Create a new tracer with pre-allocated capacity.
            pub fn with_capacity(est_instructions: usize) -> Self {
                let cap = est_instructions / 40 + 1;
                Self {
                    clock: 0,
                    max_clock_diff: DEFAULT_MAX_CLOCK_DIFF,
                    reg_clock: [0; 32],
                    mem_clock: rustc_hash::FxHashMap::default(),
                    mem_initial: rustc_hash::FxHashMap::default(),
                    program_reads: rustc_hash::FxHashMap::default(),
                    clock_update: #access_table::new(),
                    #(#external_inits,)*
                    #(#table_inits_cap,)*
                }
            }

            /// Total number of traced instructions.
            pub fn total_traces(&self) -> usize {
                0 #(#external_total_traces)* #(#total_traces_sum)*
            }

            /// The largest row count across every per-component trace table.
            ///
            /// This is the binding capacity of a segment: the prover sizes each
            /// component to a power of two at least its row count, so the
            /// fullest table is what would first overflow a row budget. A
            /// capacity-aware runner closes a segment when this reaches the
            /// budget rather than after a fixed number of cycles, which keeps
            /// every opcode/lookup mix near the budget instead of guessing a
            /// cycle count.
            pub fn max_table_len(&self) -> usize {
                let mut m = self.clock_update.len();
                #(#external_max_updates)*
                #(#opcode_max_updates)*
                m
            }

            /// Print all non-empty trace tables as DataFrames.
            ///
            /// # Arguments
            /// * `max_rows` - Maximum rows to display per table (None for default)
            /// * `max_cols` - Maximum columns to display per table (None for default)
            pub fn print_tables(&self, max_rows: Option<usize>, max_cols: Option<usize>) {
                debug_utils::set_display_options(max_rows, max_cols);
                #(#print_table_stmts)*
            }
        }
    }
}

/// Generate the trace_op! macro
pub(crate) fn generate_trace_op_macro(opcodes: &[&OpcodeDef]) -> proc_macro2::TokenStream {
    let arms: Vec<_> = opcodes
        .iter()
        .map(|op| {
            let name = &op.name;
            // Filter out clock and pc - they're added automatically
            let user_fields: Vec<_> = op
                .fields
                .iter()
                .filter(|f| {
                    let s = f.to_string();
                    s != "clock" && s != "pc"
                })
                .collect();

            let field_patterns: Vec<_> = user_fields.iter().map(|f| quote! { $#f:expr }).collect();
            let field_args: Vec<_> = user_fields.iter().map(|f| quote! { $#f }).collect();

            quote! {
                (#name: $tracer:expr, $pc:expr, #(#field_patterns),*) => {
                    $tracer.#name.push($tracer.clock, $pc, #(#field_args),*);
                };
            }
        })
        .collect();

    quote! {
        /// Trace macro for recording opcode execution.
        ///
        /// Usage: `trace_op!(opcode: tracer, pc, field1, field2, ...)`
        #[macro_export]
        macro_rules! trace_op {
            #(#arms)*
        }
    }
}

/// Proc-macro to define standalone component tables: same table syntax as
/// `define_trace_tables!` (including `derived:` and `constraints:` blocks)
/// but without the zkVM-specific `Tracer` struct and `trace_op!` macro, for
/// AIRs that are not opcode traces (e.g. the recursion verifier components).
pub fn define_component_tables(input: TokenStream) -> TokenStream {
    let def = parse_macro_input!(input as TraceTablesDef);

    let tables: Vec<_> = def.opcodes.iter().map(generate_table).collect();
    let prover_columns: Vec<_> = def
        .opcodes
        .iter()
        .map(|op| generate_prover_columns(op).unwrap_or_else(|e| e.to_compile_error()))
        .collect();
    let lookup_macros: Vec<_> = def
        .opcodes
        .iter()
        .map(|op| generate_lookup_macros(op, count_opcode_flags(&op.fields) == 0))
        .collect();

    let output = quote! {
        #(#tables)*

        pub mod prover_columns {
            // Import EvalAtRow for from_eval method
            #[allow(unused_imports)]
            use stwo_constraint_framework::EvalAtRow;

            #(#prover_columns)*
        }

        #(#lookup_macros)*
    };

    output.into()
}

/// Proc-macro to define columnar trace tables.
///
/// # Example
///
/// ```ignore
/// define_trace_tables! {
///     add: {
///         committed: { clock, pc, rd, rs1, rs2 },
///     },
///     lui: {
///         committed: {
///             clock, pc, rd, imm_0, imm_1, imm_2,
///         },
///         derived: {
///             imm: imm_0 + pow2(4) * imm_1 + pow2(12) * imm_2,
///         },
///         constraints: {
///             imm * (1 - imm),
///         },
///     },
/// }
/// ```
///
/// This generates:
/// - `AddTable`, `LuiTable` structs with columnar fields
/// - `Tracer` struct with all tables
/// - `trace_op!` macro for recording traces
/// - `prover_columns::*Columns<T>` structs with one generic method per derived
///   column and a `constraints()` method, both usable in AIR evaluation
///   (`T = E::F`) and witness generation (`T = PackedM31` via `at(i)`)
pub fn define_trace_tables(input: TokenStream) -> TokenStream {
    let def = parse_macro_input!(input as TraceTablesDef);
    let traced: Vec<_> = def.opcodes.iter().filter(|op| !op.air_only).collect();
    // `define_trace_tables!` (recursion components) has no external fn-DSL
    // tables folded into its tracer.
    let trace_tokens = generate_trace_tables_content(&def, &[], quote!(AccessTable));
    let trace_op_macro = generate_trace_op_macro(&traced);
    quote! {
        #trace_tokens
        #trace_op_macro
    }
    .into()
}

pub(crate) fn generate_trace_tables(
    def: &TraceTablesDef,
    externals: &[ExternalTable],
    access_table: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    generate_trace_tables_content(def, externals, access_table)
}

fn generate_trace_tables_content(
    def: &TraceTablesDef,
    externals: &[ExternalTable],
    access_table: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let traced: Vec<&OpcodeDef> = def.opcodes.iter().filter(|op| !op.air_only).collect();
    let tables: Vec<_> = traced.iter().map(|op| generate_table(op)).collect();
    let tracer = generate_tracer(&traced, externals, access_table);

    // Re-export each external fn-DSL table's columns beside the opcode ones.
    let external_columns_reexports: Vec<_> = externals
        .iter()
        .map(|ext| {
            let columns = ext.columns_type();
            quote! { pub use #columns; }
        })
        .collect();

    // Generate prover columns; expression errors surface as compile errors
    // pointing at the offending formula.
    let prover_columns: Vec<_> = def
        .opcodes
        .iter()
        .map(|op| generate_prover_columns(op).unwrap_or_else(|e| e.to_compile_error()))
        .collect();
    let lookup_macros: Vec<_> = def
        .opcodes
        .iter()
        .map(|op| generate_lookup_macros(op, count_opcode_flags(&op.fields) == 0))
        .collect();

    quote! {
        // Runner code (existing)
        #(#tables)*
        #tracer

        // Prover columns (NEW)
        pub mod prover_columns {
            // Import EvalAtRow for from_eval method
            #[allow(unused_imports)]
            use stwo_constraint_framework::EvalAtRow;

            // External fn-DSL columns (felt-generated, e.g. Poseidon2Columns),
            // re-exported beside the opcode table columns.
            #(#external_columns_reexports)*

            #(#prover_columns)*
        }

        #(#lookup_macros)*
    }
}
