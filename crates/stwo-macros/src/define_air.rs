//! Unified AIR schema proc-macro: relations, preprocessed lookups, and trace tables.

use proc_macro::TokenStream;
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{Expr, Ident, Token, braced, parse_macro_input};

use crate::relations::{RelationsInput, generate_relations, parse_relation_defs};
use crate::trace_tables::{
    ExternalTable, TraceTablesDef, generate_trace_op_macro, generate_trace_tables,
    parse_opcode_defs,
};

/// Single source of truth for zkVM AIR metadata.
struct AirInput {
    relations: RelationsInput,
    clock_gap: Option<ClockGapInput>,
    /// External fn-DSL trace tables folded into the `Tracer` (e.g. poseidon2).
    externals: Vec<ExternalTable>,
    opcodes: Vec<crate::trace_tables::OpcodeDef>,
}

struct ClockGapInput {
    bound_by: Ident,
    relation: Ident,
    max_delta: Expr,
}

impl ClockGapInput {
    fn derive_max_delta(bound_by: &Ident) -> syn::Result<Expr> {
        let name = bound_by.to_string();
        let digits: String = name
            .chars()
            .rev()
            .take_while(|ch| ch.is_ascii_digit())
            .collect::<String>()
            .chars()
            .rev()
            .collect();
        if digits.is_empty() {
            return Err(syn::Error::new(
                bound_by.span(),
                "`clock_gap.bound_by` needs `max_delta` unless the relation name ends in a bit width",
            ));
        }
        let bits: u32 = digits.parse().map_err(|_| {
            syn::Error::new(bound_by.span(), "failed to parse range-check bit width")
        })?;
        let expr: Expr = syn::parse_quote!((1 << #bits) - 1);
        Ok(expr)
    }
}

impl Parse for ClockGapInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut bound_by = None;
        let mut relation = None;
        let mut max_delta = None;

        while !input.is_empty() {
            let key: Ident = input.parse()?;
            input.parse::<Token![:]>()?;
            match key.to_string().as_str() {
                "bound_by" => {
                    if bound_by.is_some() {
                        return Err(syn::Error::new(key.span(), "duplicate `bound_by`"));
                    }
                    bound_by = Some(input.parse()?);
                }
                "relation" => {
                    if relation.is_some() {
                        return Err(syn::Error::new(key.span(), "duplicate `relation`"));
                    }
                    relation = Some(input.parse()?);
                }
                "max_delta" => {
                    if max_delta.is_some() {
                        return Err(syn::Error::new(key.span(), "duplicate `max_delta`"));
                    }
                    max_delta = Some(input.parse()?);
                }
                other => {
                    return Err(syn::Error::new(
                        key.span(),
                        format!(
                            "unknown clock_gap key `{other}`, expected `bound_by`, `relation`, or `max_delta`"
                        ),
                    ));
                }
            }
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }
        }

        let bound_by = bound_by.ok_or_else(|| {
            syn::Error::new(
                proc_macro2::Span::call_site(),
                "`clock_gap` needs `bound_by: <preprocessed_relation>`",
            )
        })?;
        let relation = relation.unwrap_or_else(|| syn::parse_quote!(memory_access));
        let max_delta = match max_delta {
            Some(expr) => expr,
            None => Self::derive_max_delta(&bound_by)?,
        };
        Ok(Self {
            bound_by,
            relation,
            max_delta,
        })
    }
}

impl Parse for AirInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut relations = None;
        let mut preprocessed = None;
        let mut clock_gap = None;
        let mut opcodes = None;
        let mut externals: Vec<ExternalTable> = Vec::new();

        while !input.is_empty() {
            let label: Ident = input.parse()?;
            input.parse::<Token![:]>()?;
            let content;
            braced!(content in input);
            match label.to_string().as_str() {
                "relations" => {
                    if relations.is_some() {
                        return Err(syn::Error::new(
                            label.span(),
                            "duplicate `relations:` block",
                        ));
                    }
                    relations = Some(parse_relation_defs(&content)?);
                }
                "preprocessed" => {
                    if preprocessed.is_some() {
                        return Err(syn::Error::new(
                            label.span(),
                            "duplicate `preprocessed:` block",
                        ));
                    }
                    preprocessed = Some(parse_relation_defs(&content)?);
                }
                "trace" => {
                    if opcodes.is_some() {
                        return Err(syn::Error::new(label.span(), "duplicate `trace:` block"));
                    }
                    opcodes = Some(parse_opcode_defs(&content)?);
                }
                "clock_gap" => {
                    if clock_gap.is_some() {
                        return Err(syn::Error::new(
                            label.span(),
                            "duplicate `clock_gap:` block",
                        ));
                    }
                    clock_gap = Some(content.parse::<ClockGapInput>()?);
                }
                "external" => {
                    if !externals.is_empty() {
                        return Err(syn::Error::new(label.span(), "duplicate `external:` block"));
                    }
                    // `name: module::path` entries — fn-DSL tables folded into
                    // the Tracer (e.g. `poseidon2: crate::poseidon2`).
                    while !content.is_empty() {
                        let field: Ident = content.parse()?;
                        content.parse::<Token![:]>()?;
                        let module: syn::Path = content.parse()?;
                        externals.push(ExternalTable { field, module });
                        if content.peek(Token![,]) {
                            content.parse::<Token![,]>()?;
                        }
                    }
                }
                other => {
                    return Err(syn::Error::new(
                        label.span(),
                        format!(
                            "unknown section `{other}`, expected `relations:`, `preprocessed:`, `external:`, `clock_gap:`, or `trace:`"
                        ),
                    ));
                }
            }
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }
        }

        let relations = relations.ok_or_else(|| {
            syn::Error::new(
                proc_macro2::Span::call_site(),
                "missing `relations: { ... }` section",
            )
        })?;
        let preprocessed = preprocessed.ok_or_else(|| {
            syn::Error::new(
                proc_macro2::Span::call_site(),
                "missing `preprocessed: { ... }` section",
            )
        })?;
        let opcodes = opcodes.ok_or_else(|| {
            syn::Error::new(
                proc_macro2::Span::call_site(),
                "missing `trace: { ... }` section",
            )
        })?;

        Ok(AirInput {
            relations: RelationsInput {
                relations,
                preprocessed,
            },
            clock_gap,
            externals,
            opcodes,
        })
    }
}

pub fn define_air(input: TokenStream) -> TokenStream {
    let AirInput {
        relations,
        clock_gap,
        externals,
        mut opcodes,
    } = parse_macro_input!(input as AirInput);

    let relations_tokens = generate_relations(&relations);
    let max_clock_delta = if let Some(clock_gap) = &clock_gap {
        let bound_by = &clock_gap.bound_by;
        if !relations
            .preprocessed
            .iter()
            .any(|relation| relation.name == *bound_by)
        {
            return syn::Error::new(
                bound_by.span(),
                "`clock_gap.bound_by` must name a preprocessed relation",
            )
            .to_compile_error()
            .into();
        }
        let relation = &clock_gap.relation;
        if !relations
            .relations
            .iter()
            .any(|declared| declared.name == *relation)
        {
            return syn::Error::new(
                relation.span(),
                "`clock_gap.relation` must name a declared relation",
            )
            .to_compile_error()
            .into();
        }
        let max_delta = &clock_gap.max_delta;
        let clock_update: crate::trace_tables::OpcodeDef = syn::parse_quote! {
            air clock_update: {
                committed: {
                    addr_space, addr, clock_prev,
                    value_0, value_1, value_2, value_3,
                },
                lookups: {
                    -enabler * #relation(addr_space, addr, clock_prev, value_0, value_1, value_2, value_3),
                    enabler * #relation(addr_space, addr, clock_prev + constant(crate::schema::trace::CLOCK_GAP_MAX_DELTA), value_0, value_1, value_2, value_3),
                },
            }
        };
        opcodes.push(clock_update);
        quote!(#max_delta)
    } else {
        quote!((1 << 20) - 1)
    };
    let trace_def = TraceTablesDef::from_trace(opcodes, &relations.preprocessed);
    let traced: Vec<_> = trace_def.opcodes.iter().filter(|op| !op.air_only).collect();
    let trace_op_macro = generate_trace_op_macro(&traced);
    // Re-export each external fn-DSL table type into the `trace` module so the
    // runner names it as `air::trace::<Table>` like any opcode table.
    let external_table_reexports: Vec<_> = externals
        .iter()
        .map(|ext| {
            let table_type = ext.table_type();
            quote! { pub use #table_type; }
        })
        .collect();
    let trace_tokens =
        generate_trace_tables(&trace_def, &externals, quote!(crate::trace::ClockGapTable));

    quote! {
        #trace_op_macro

        pub mod relations {
            //! LogUp relation registry for zkVM trace tables and prover components.

            #![allow(non_camel_case_types)]

            // The interaction transcript is part of the proof protocol, so its
            // grinding difficulty cannot depend on the compiler optimization profile.
            pub const INTERACTION_POW_BITS: u32 = 10;

            #relations_tokens
        }

        pub mod trace {
            #![allow(clippy::too_many_arguments)]
            //! Trace capture for zkVM execution.

            use simd::AlignedVec;
            use crate::trace::Access;

            #(#external_table_reexports)*

            /// Maximum clock delta represented by one synthetic clock-gap row.
            pub const CLOCK_GAP_MAX_DELTA: u32 = #max_clock_delta;

            /// Compatibility name for runner code and tests.
            pub const DEFAULT_MAX_CLOCK_DIFF: u32 = CLOCK_GAP_MAX_DELTA;

            #trace_tokens
        }
    }
    .into()
}
