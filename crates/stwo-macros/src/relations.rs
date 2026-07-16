//! Proc-macro for generating Relations struct and preprocessed table infrastructure.

use proc_macro::TokenStream;
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{Attribute, Ident, Token, braced};

/// A single relation definition: `name: field1, field2, ...;`
pub(crate) struct RelationDef {
    pub(crate) attrs: Vec<Attribute>,
    pub(crate) name: Ident,
    pub(crate) fields: Vec<Ident>,
}

impl Parse for RelationDef {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let name: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let fields: Punctuated<Ident, Token![,]> = Punctuated::parse_separated_nonempty(input)?;
        // Optional trailing semicolon handled by parent
        Ok(RelationDef {
            attrs,
            name,
            fields: fields.into_iter().collect(),
        })
    }
}

/// Input for relations macro:
/// ```ignore
/// relations {
///     name1: field1, field2;
///     name2: field3, field4;
/// }
/// preprocessed {
///     prep1: col1, col2;
/// }
/// ```
pub(crate) struct RelationsInput {
    pub(crate) relations: Vec<RelationDef>,
    pub(crate) preprocessed: Vec<RelationDef>,
}

pub(crate) fn parse_relation_defs(input: ParseStream) -> syn::Result<Vec<RelationDef>> {
    let mut relations = Vec::new();
    while !input.is_empty() {
        relations.push(input.parse::<RelationDef>()?);
        let _ = input.parse::<Token![;]>();
    }
    Ok(relations)
}

impl Parse for RelationsInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // Parse "relations { ... }"
        let relations_ident: Ident = input.parse()?;
        if relations_ident != "relations" {
            return Err(syn::Error::new(
                relations_ident.span(),
                "expected 'relations'",
            ));
        }
        let relations_content;
        braced!(relations_content in input);
        let relations = parse_relation_defs(&relations_content)?;

        // Parse "preprocessed { ... }"
        let preprocessed_ident: Ident = input.parse()?;
        if preprocessed_ident != "preprocessed" {
            return Err(syn::Error::new(
                preprocessed_ident.span(),
                "expected 'preprocessed'",
            ));
        }
        let preprocessed_content;
        braced!(preprocessed_content in input);
        let preprocessed = parse_relation_defs(&preprocessed_content)?;

        Ok(RelationsInput {
            relations,
            preprocessed,
        })
    }
}

pub(crate) fn generate_relations(input: &RelationsInput) -> proc_macro2::TokenStream {
    let RelationsInput {
        relations,
        preprocessed,
    } = input;
    // Generate relation wrapper types
    let relation_wrapper_types = relations.iter().map(|rel| {
        let name = &rel.name;
        let attrs = &rel.attrs;
        let field_count = rel.fields.len();
        quote! {
            #(#attrs)*
            #[derive(Clone, Debug, PartialEq)]
            pub struct #name(
                pub stwo_constraint_framework::logup::LookupElements<#field_count>
            );

            impl #name {
                pub fn dummy() -> Self {
                    Self(stwo_constraint_framework::logup::LookupElements::dummy())
                }

                pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
                    Self(stwo_constraint_framework::logup::LookupElements::draw(channel))
                }
            }

            impl<F: Clone, EF: stwo_constraint_framework::RelationEFTraitBound<F>>
                stwo_constraint_framework::Relation<F, EF> for #name
            {
                fn combine(&self, values: &[F]) -> EF {
                    self.0.combine(values)
                }

                fn get_name(&self) -> &str {
                    stringify!(#name)
                }

                fn get_size(&self) -> usize {
                    #field_count
                }
            }
        }
    });

    let preprocessed_wrapper_types = preprocessed.iter().map(|prep| {
        let name = &prep.name;
        let attrs = &prep.attrs;
        let col_count = prep.fields.len();
        quote! {
            #(#attrs)*
            #[derive(Clone, Debug, PartialEq)]
            pub struct #name(
                pub stwo_constraint_framework::logup::LookupElements<#col_count>
            );

            impl #name {
                pub fn dummy() -> Self {
                    Self(stwo_constraint_framework::logup::LookupElements::dummy())
                }

                pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
                    Self(stwo_constraint_framework::logup::LookupElements::draw(channel))
                }
            }

            impl<F: Clone, EF: stwo_constraint_framework::RelationEFTraitBound<F>>
                stwo_constraint_framework::Relation<F, EF> for #name
            {
                fn combine(&self, values: &[F]) -> EF {
                    self.0.combine(values)
                }

                fn get_name(&self) -> &str {
                    stringify!(#name)
                }

                fn get_size(&self) -> usize {
                    #col_count
                }
            }
        }
    });

    // Generate top-level relation types (duplicated for backwards compat)
    let toplevel_relation_types = relations.iter().map(|rel| {
        let name = &rel.name;
        let field_count = rel.fields.len();
        quote! {
            #[allow(non_camel_case_types)]
            #[derive(Clone, Debug, PartialEq)]
            pub struct #name(
                stwo_constraint_framework::logup::LookupElements<#field_count>
            );

            impl #name {
                pub fn dummy() -> Self {
                    Self(stwo_constraint_framework::logup::LookupElements::dummy())
                }
                pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
                    Self(stwo_constraint_framework::logup::LookupElements::draw(channel))
                }
                pub fn combine<F, EF>(&self, values: &[F]) -> EF
                where
                    F: Clone,
                    EF: stwo_constraint_framework::RelationEFTraitBound<F>,
                {
                    self.0.combine(values)
                }
            }

            impl<F, EF> stwo_constraint_framework::Relation<F, EF> for #name
            where
                F: Clone,
                EF: stwo_constraint_framework::RelationEFTraitBound<F>,
            {
                fn combine(&self, values: &[F]) -> EF {
                    self.0.combine(values)
                }

                fn get_name(&self) -> &str {
                    stringify!(#name)
                }

                fn get_size(&self) -> usize {
                    #field_count
                }
            }
        }
    });

    let toplevel_prep_types = preprocessed.iter().map(|prep| {
        let name = &prep.name;
        let col_count = prep.fields.len();
        quote! {
            #[allow(non_camel_case_types)]
            #[derive(Clone, Debug, PartialEq)]
            pub struct #name(
                stwo_constraint_framework::logup::LookupElements<#col_count>
            );

            impl #name {
                pub fn dummy() -> Self {
                    Self(stwo_constraint_framework::logup::LookupElements::dummy())
                }
                pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
                    Self(stwo_constraint_framework::logup::LookupElements::draw(channel))
                }
                pub fn combine<F, EF>(&self, values: &[F]) -> EF
                where
                    F: Clone,
                    EF: stwo_constraint_framework::RelationEFTraitBound<F>,
                {
                    self.0.combine(values)
                }
            }

            impl<F, EF> stwo_constraint_framework::Relation<F, EF> for #name
            where
                F: Clone,
                EF: stwo_constraint_framework::RelationEFTraitBound<F>,
            {
                fn combine(&self, values: &[F]) -> EF {
                    self.0.combine(values)
                }

                fn get_name(&self) -> &str {
                    stringify!(#name)
                }

                fn get_size(&self) -> usize {
                    #col_count
                }
            }
        }
    });

    // Generate Relations struct fields
    let relations_struct_fields = relations.iter().map(|rel| {
        let name = &rel.name;
        let fields = &rel.fields;
        let doc = format!(
            "Relation: ({})",
            fields
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        quote! {
            #[doc = #doc]
            pub #name: relation_types::#name,
        }
    });

    let preprocessed_struct_fields = preprocessed.iter().map(|prep| {
        let name = &prep.name;
        let cols = &prep.fields;
        let doc = format!(
            "Preprocessed relation: ({})",
            cols.iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        quote! {
            #[doc = #doc]
            pub #name: relation_types::#name,
        }
    });

    // Generate Relations::dummy() initializers
    let relations_dummy_inits = relations.iter().map(|rel| {
        let name = &rel.name;
        quote! { #name: relation_types::#name::dummy(), }
    });

    let preprocessed_dummy_inits = preprocessed.iter().map(|prep| {
        let name = &prep.name;
        quote! { #name: relation_types::#name::dummy(), }
    });

    // Generate Relations::draw() initializers
    let relations_draw_inits = relations.iter().map(|rel| {
        let name = &rel.name;
        quote! { #name: relation_types::#name::draw(channel), }
    });

    let preprocessed_draw_inits = preprocessed.iter().map(|prep| {
        let name = &prep.name;
        quote! { #name: relation_types::#name::draw(channel), }
    });

    // The verifier consumes relation challenges by transcript position. Emit
    // the registry from the same declarations and in the same order as
    // `Relations::draw`, so downstream code never duplicates that mapping.
    let relation_descriptors = relations.iter().chain(preprocessed).map(|relation| {
        let name = &relation.name;
        let size = relation.fields.len();
        quote! {
            RelationDescriptor {
                name: stringify!(#name),
                size: #size,
            }
        }
    });
    let relation_count = relations.len() + preprocessed.len();

    // Generate PreProcessedTrace extensions
    let preprocessed_trace_extends = preprocessed.iter().map(|prep| {
        let name = &prep.name;
        quote! {
            trace.extend(crate::preprocessed::#name::Table::gen_columns());
            ids.extend(crate::preprocessed::#name::Table::column_ids());
        }
    });
    let preprocessed_id_extends = preprocessed.iter().map(|prep| {
        let name = &prep.name;
        quote! {
            ids.extend(crate::preprocessed::#name::Table::column_ids());
        }
    });
    let preprocessed_log_size_extends = preprocessed.iter().map(|prep| {
        let name = &prep.name;
        quote! {
            sizes.extend(
                std::iter::repeat(
                    <crate::preprocessed::#name::Table as PreprocessedTable>::LOG_SIZE,
                )
                .take(crate::preprocessed::#name::Table::column_ids().len()),
            );
        }
    });

    // Generate Counters struct fields
    let counters_fields = preprocessed.iter().map(|prep| {
        let name = &prep.name;
        let cols = &prep.fields;
        let doc = format!(
            "Counter for {}: ({})",
            name,
            cols.iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        quote! {
            #[doc = #doc]
            pub #name: Counter<crate::preprocessed::#name::Table>,
        }
    });

    // Generate Counters::new() initializers
    let counters_new_inits = preprocessed.iter().map(|prep| {
        let name = &prep.name;
        quote! { #name: Counter::new(), }
    });

    // Generate Counters::into_traces() extends
    let counters_into_traces = preprocessed.iter().map(|prep| {
        let name = &prep.name;
        quote! { traces.extend(self.#name.into_trace()); }
    });

    // Generate Counters::print_counters() bodies
    let counters_print_bodies = preprocessed.iter().map(|prep| {
        let name = &prep.name;
        let name_str = name.to_string();
        quote! {
            let table_name = #name_str;
            let non_zero_count = self.#name.counts.iter().filter(|c| **c > 0).count();
            if non_zero_count > 0 {
                println!("\n=== {} ({} non-zero entries) ===", table_name, non_zero_count);
                let entries: Vec<(usize, u32)> = self.#name.counts
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| **c > 0)
                    .map(|(i, c)| (i, *c))
                    .collect();
                let max = max_rows.unwrap_or(entries.len());
                for (idx, count) in entries.iter().take(max) {
                    println!("  [{}] = {}", idx, count);
                }
                if entries.len() > max {
                    println!("  ... ({} more)", entries.len() - max);
                }
            }
        }
    });

    quote! {
        use std::marker::PhantomData;
        use simd::AlignedVec;
        use stwo::core::ColumnVec;
        use stwo::core::fields::m31::BaseField;
        use stwo::core::poly::circle::CanonicCoset;
        use stwo::prover::backend::simd::SimdBackend;
        use stwo::prover::backend::simd::column::BaseColumn;
        use stwo::prover::backend::simd::m31::PackedM31;
        use stwo::prover::poly::BitReversedOrder;
        use stwo::prover::poly::circle::CircleEvaluation;
        use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

        // ==================== Relation Wrapper Types ====================
        pub mod relation_types {
            #(#relation_wrapper_types)*
            #(#preprocessed_wrapper_types)*
        }

        // ==================== Top-level Relation Types ====================
        #(#toplevel_relation_types)*
        #(#toplevel_prep_types)*

        // ==================== Relations Struct ====================
        /// One relation challenge in the exact order consumed by `Relations::draw`.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct RelationDescriptor {
            pub name: &'static str,
            pub size: usize,
        }

        #[derive(Clone)]
        pub struct Relations {
            #(#relations_struct_fields)*
            #(#preprocessed_struct_fields)*
        }

        impl Relations {
            /// Fixed relation registry shared by transcript planning and AIR evaluation.
            pub const DESCRIPTORS: [RelationDescriptor; #relation_count] = [
                #(#relation_descriptors,)*
            ];

            pub fn dummy() -> Self {
                Self {
                    #(#relations_dummy_inits)*
                    #(#preprocessed_dummy_inits)*
                }
            }

            pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
                Self {
                    #(#relations_draw_inits)*
                    #(#preprocessed_draw_inits)*
                }
            }
        }

        // ==================== Preprocessed Tables ====================

        /// Trait for preprocessed table generation.
        pub trait PreprocessedTable {
            const LOG_SIZE: u32;
            fn index(values: &[PackedM31]) -> [u32; 16];
            fn gen_columns() -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>;
            fn column_ids() -> Vec<PreProcessedColumnId>;
        }

        /// Generic counter for tracking multiplicities.
        pub struct Counter<T: PreprocessedTable> {
            pub counts: AlignedVec<u32>,
            _marker: PhantomData<T>,
        }

        impl<T: PreprocessedTable> Counter<T> {
            pub fn new() -> Self {
                let size = 1 << T::LOG_SIZE;
                let mut counts = AlignedVec::with_capacity(size);
                counts.resize(size, 0);
                Self {
                    counts,
                    _marker: PhantomData,
                }
            }

            #[inline]
            pub fn register(&mut self, num: PackedM31, denom: &[PackedM31]) {
                let num_arr = num.to_array();
                // Skip lanes with zero numerator before computing indices
                let indices = T::index(denom);
                const P: u64 = (1 << 31) - 1;
                for (lane, &n) in num_arr.iter().enumerate() {
                    if n.0 == 0 {
                        continue;
                    }
                    let idx = indices[lane];
                    debug_assert!((idx as usize) < self.counts.len(), "index {idx} out of bounds");
                    self.counts[idx as usize] =
                        ((self.counts[idx as usize] as u64 + n.0 as u64) % P) as u32;
                }
            }

            pub fn register_many(&mut self, num: &[PackedM31], denom: &[&[PackedM31]]) {
                if denom.is_empty() {
                    return;
                }
                let len = denom[0].len();
                debug_assert!(num.len() == len, "num length mismatch");
                debug_assert!(denom.iter().all(|c| c.len() == len), "column length mismatch");
                const P: u64 = (1 << 31) - 1;
                for i in 0..len {
                    let num_arr = num[i].to_array();
                    let values: Vec<PackedM31> = denom.iter().map(|c| c[i]).collect();
                    let indices = T::index(&values);
                    for (lane, &n) in num_arr.iter().enumerate() {
                        if n.0 == 0 {
                            continue;
                        }
                        let idx = indices[lane];
                        debug_assert!((idx as usize) < self.counts.len(), "index {idx} out of bounds");
                        self.counts[idx as usize] =
                            ((self.counts[idx as usize] as u64 + n.0 as u64) % P) as u32;
                    }
                }
            }

            pub fn into_trace(self) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
                let domain = CanonicCoset::new(T::LOG_SIZE).circle_domain();
                let col: BaseColumn = self.counts.into();
                vec![CircleEvaluation::new(domain, col)]
            }
        }

        impl<T: PreprocessedTable> Default for Counter<T> {
            fn default() -> Self {
                Self::new()
            }
        }

        /// Preprocessed trace containing all constant lookup tables.
        pub struct PreProcessedTrace {
            pub trace: ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
            pub ids: Vec<PreProcessedColumnId>,
        }

        impl PreProcessedTrace {
            /// Column registry without materializing the potentially large tables.
            pub fn column_ids() -> Vec<PreProcessedColumnId> {
                let mut ids = vec![];
                #(#preprocessed_id_extends)*
                ids
            }

            /// Committed log size for each column in `column_ids` order.
            pub fn column_log_sizes() -> Vec<u32> {
                let mut sizes = vec![];
                #(#preprocessed_log_size_extends)*
                sizes
            }

            pub fn new() -> Self {
                let mut trace = vec![];
                let mut ids = vec![];
                #(#preprocessed_trace_extends)*
                Self { trace, ids }
            }
        }

        impl Default for PreProcessedTrace {
            fn default() -> Self {
                Self::new()
            }
        }

        /// Aggregate of all multiplicity counters.
        pub struct Counters {
            #(#counters_fields)*
        }

        impl Counters {
            pub fn new() -> Self {
                Self {
                    #(#counters_new_inits)*
                }
            }

            pub fn into_traces(self) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
                let mut traces = vec![];
                #(#counters_into_traces)*
                traces
            }

            pub fn print_counters(&self, max_rows: Option<usize>, _max_cols: Option<usize>) {
                debug_utils::set_display_options(max_rows, None);
                #(#counters_print_bodies)*
            }
        }

        impl Default for Counters {
            fn default() -> Self {
                Self::new()
            }
        }
    }
}

pub fn relations(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as RelationsInput);
    generate_relations(&input).into()
}
