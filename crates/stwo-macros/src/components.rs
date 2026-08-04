//! Proc-macros for generating AIR component infrastructure.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{Ident, Path, Token, braced};

/// Convert snake_case to PascalCase
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
// components! macros
// =============================================================================

struct ComponentEntry {
    name: Ident,
    module: Path,
    /// Bare entries get their whole component module (AIR + witness)
    /// generated from the table's `define_air!` declaration.
    /// `name: module` entries reuse a component generated through the AIR DSL
    /// in its owning crate.
    generated: bool,
}

impl Parse for ComponentEntry {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let first: Path = input.parse()?;
        let name = path_name(&first)?;
        let (module, generated) = if input.peek(Token![:]) {
            input.parse::<Token![:]>()?;
            (input.parse()?, false)
        } else {
            (first, true)
        };
        Ok(Self {
            name,
            module,
            generated,
        })
    }
}

fn path_name(path: &Path) -> syn::Result<Ident> {
    path.segments
        .last()
        .map(|segment| segment.ident.clone())
        .ok_or_else(|| syn::Error::new_spanned(path, "component path must have a final segment"))
}

/// Input for trace-backed component lists: `component, nested::component, ...`
struct ComponentList {
    components: Vec<ComponentEntry>,
}

struct ComponentsInput {
    trace: Vec<ComponentEntry>,
    lookup: Vec<Ident>,
}

struct IdentList {
    idents: Vec<Ident>,
}

impl Parse for IdentList {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let idents: Punctuated<Ident, Token![,]> = Punctuated::parse_terminated(input)?;
        Ok(Self {
            idents: idents.into_iter().collect(),
        })
    }
}

impl Parse for ComponentList {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let components: Punctuated<ComponentEntry, Token![,]> =
            Punctuated::parse_terminated(input)?;
        Ok(ComponentList {
            components: components.into_iter().collect(),
        })
    }
}

impl Parse for ComponentsInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let trace_label: Ident = input.parse()?;
        if trace_label != "trace" {
            return Err(syn::Error::new_spanned(
                trace_label,
                "expected `trace: { ... }` section",
            ));
        }
        input.parse::<Token![:]>()?;
        let trace_content;
        braced!(trace_content in input);
        let ComponentList { components: trace } = trace_content.parse()?;

        input.parse::<Token![,]>()?;

        let lookup_label: Ident = input.parse()?;
        if lookup_label != "lookup" {
            return Err(syn::Error::new_spanned(
                lookup_label,
                "expected `lookup: { ... }` section",
            ));
        }
        input.parse::<Token![:]>()?;
        let lookup_content;
        braced!(lookup_content in input);
        let IdentList { idents: lookup } = lookup_content.parse()?;
        let _ = input.parse::<Token![,]>();

        Ok(Self { trace, lookup })
    }
}

pub fn components(input: TokenStream) -> TokenStream {
    let ComponentsInput { trace, lookup } = syn::parse_macro_input!(input as ComponentsInput);
    let lookup_components = render_lookup_components(&lookup);
    let trace_components = render_trace_components(&trace);
    let components = render_components(trace, lookup);
    quote! {
        pub mod lookups {
            #lookup_components
        }

        #trace_components

        #components
    }
    .into()
}

/// Render the whole component module (air + witness) of every generated
/// trace component: the `Eval` shell around the table's `constraints()` and
/// the exported lookup macros — everything else about the component already
/// lives in its `define_trace_tables!` declaration.
fn render_trace_components(entries: &[ComponentEntry]) -> TokenStream2 {
    let modules = entries.iter().filter(|entry| entry.generated).map(|entry| {
        let name = &entry.name;
        let columns_type = format_ident!("{}Columns", to_pascal_case(&name.to_string()));
        let lookups_macro = format_ident!("{}_lookups", name);
        let dynamic_lookups_macro = format_ident!("{}_dynamic_lookups", name);
        let interaction_macro = format_ident!("{}_interaction", name);
        let register_macro = format_ident!("{}_register_multiplicities", name);
        let doc = format!(
            "{name} component, generated from its `define_trace_tables!` declaration."
        );
        quote! {
            #[doc = #doc]
            pub mod #name {
                pub mod air {
                    use air::relation_eval::{
                        DynamicRelationEvalAtRow, DynamicRelationFrameworkEval,
                    };
                    use stwo_constraint_framework::{EvalAtRow, FrameworkComponent, FrameworkEval};

                    use crate::relations::Relations;
                    use air::trace::prover_columns::#columns_type;

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
                            for constraint in cols.constraints() {
                                eval.add_constraint(constraint);
                            }
                            air::#lookups_macro!(eval, cols, self.relations);
                            eval
                        }
                    }

                    impl DynamicRelationFrameworkEval for Eval {
                        fn evaluate_dynamic_relations<E: DynamicRelationEvalAtRow>(
                            &self,
                            mut eval: E,
                        ) -> E {
                            let cols = #columns_type::from_eval(&mut eval);
                            for constraint in cols.constraints() {
                                eval.add_constraint(constraint);
                            }
                            air::#dynamic_lookups_macro!(eval, cols);
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
                    use stwo::prover::poly::BitReversedOrder;
                    use stwo::prover::poly::circle::CircleEvaluation;

                    #[allow(unused_imports)]
                    use air::trace::prover_columns::#columns_type;

                    /// LogUp interaction trace from the table's `lookups:`
                    /// declaration — the same entries the AIR consumes, so
                    /// order and pairing match by construction.
                    pub fn gen_interaction_trace(
                        trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
                        relations: &crate::relations::Relations,
                    ) -> (
                        ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
                        QM31,
                    ) {
                        if trace.is_empty() {
                            return (vec![], QM31::zero());
                        }
                        air::#interaction_macro!(trace, relations)
                    }

                    /// Preprocessed multiplicity registration for the
                    /// `preprocessed`-marked lookup entries.
                    pub fn register_multiplicities(
                        trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
                        counters: &mut crate::relations::Counters,
                    ) {
                        if trace.is_empty() {
                            return;
                        }
                        air::#register_macro!(trace, counters);
                    }
                }

                #[cfg(test)]
                mod tests {
                    use num_traits::Zero;
                    use stwo::core::poly::circle::CanonicCoset;
                    use stwo::prover::backend::Column;
                    use stwo::prover::backend::simd::column::BaseColumn;
                    use stwo::prover::poly::circle::CircleEvaluation;

                    use air::trace::prover_columns::#columns_type;

                    /// Padding rows (enabler = 0) contribute nothing to the
                    /// LogUp sum.
                    #[test]
                    fn padding_only_trace_interaction_sum_is_zero() {
                        let log_size = 4u32;
                        let domain = CanonicCoset::new(log_size).circle_domain();
                        let trace: Vec<_> = (0..#columns_type::<()>::SIZE)
                            .map(|_| CircleEvaluation::new(domain, BaseColumn::zeros(1 << log_size)))
                            .collect();
                        let relations = crate::relations::Relations::dummy();
                        let (interaction, claimed_sum) =
                            super::witness::gen_interaction_trace(&trace, &relations);
                        assert!(!interaction.is_empty());
                        assert!(claimed_sum.is_zero());
                    }
                }
            }
        }
    });
    // Override entries (`name: module`) don't generate a module; alias the
    // pointed-at module as `#name` so `crate::components::#name::{air,witness}`
    // resolves uniformly (used by the e2e test harness and trace orchestration).
    let aliases = entries
        .iter()
        .filter(|entry| !entry.generated)
        .map(|entry| {
            let name = &entry.name;
            let module = &entry.module;
            quote! { pub use #module as #name; }
        });

    quote! {
        #(#modules)*
        #(#aliases)*
    }
}

fn render_components(opcodes: Vec<ComponentEntry>, lookups: Vec<Ident>) -> TokenStream2 {
    // Generate Traces struct fields
    let traces_fields = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! {
            pub #op: ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
        }
    });
    let lookup_traces_fields = lookups.iter().map(|lookup| {
        quote! {
            pub #lookup: ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
        }
    });
    let trace_table_coverage_fields = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! {
            #op: _,
        }
    });

    // Generate Traces::max_log_size() and log_sizes() body
    let log_sizes_body = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! {
            if let Some(first) = self.#op.first() {
                sizes.push(first.domain.log_size());
            }
        }
    });
    let lookup_log_sizes_body = lookups.iter().map(|lookup| {
        quote! {
            if let Some(first) = self.#lookup.first() {
                sizes.push(first.domain.log_size());
            }
        }
    });

    // Generate Traces::columns_cloned() body
    let columns_cloned_body = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! {
            columns.extend(self.#op.clone());
        }
    });
    let lookup_columns_cloned_body = lookups.iter().map(|lookup| {
        quote! {
            columns.extend(self.#lookup.clone());
        }
    });

    // Generate Traces::into_columns() body
    let into_columns_body = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! {
            columns.extend(self.#op);
        }
    });
    let lookup_into_columns_body = lookups.iter().map(|lookup| {
        quote! {
            columns.extend(self.#lookup);
        }
    });

    // Generate Traces::print_tables() body
    let print_tables_body = opcodes.iter().map(|component| {
        let op = &component.name;
        let op_str = op.to_string();
        let pascal = to_pascal_case(&op_str);
        let columns_type = format_ident!("{}Columns", pascal);
        quote! {
            if !self.#op.is_empty() {
                let table_name = #op_str;
                let names = air::trace::prover_columns::#columns_type::<()>::NAMES;
                let table = self.#op.to_table_named(names);
                println!("\n=== {} ({} rows) ===", table_name, self.#op.first().unwrap().values.to_cpu().len());
                println!("{}", table);
            }
        }
    });
    let lookup_print_tables_body = lookups.iter().map(|lookup| {
        let lookup_str = lookup.to_string();
        quote! {
            if !self.#lookup.is_empty() {
                let table_name = #lookup_str;
                let column_ids = crate::preprocessed::#lookup::Table::column_ids();
                let names: Vec<&str> = column_ids.iter().map(|id| id.id.as_str()).collect();
                let table = self.#lookup.to_table_named(&names);
                println!("\n=== {} ({} rows) ===", table_name, self.#lookup.first().unwrap().values.to_cpu().len());
                println!("{}", table);
            }
        }
    });

    // Generate Claim struct fields and From impl
    let claim_fields = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! { pub #op: u32, }
    });
    let lookup_claim_fields = lookups.iter().map(|lookup| {
        quote! { pub #lookup: u32, }
    });

    let claim_from_body = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! {
            #op: traces.#op
                .first()
                .map(|eval| eval.domain.log_size())
                .unwrap_or(0),
        }
    });
    let lookup_claim_from_body = lookups.iter().map(|lookup| {
        quote! {
            #lookup: traces.#lookup
                .first()
                .map(|eval| eval.domain.log_size())
                .unwrap_or(0),
        }
    });

    // Generate Claim::mix_into() body
    let claim_mix_into_body = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! {
            channel.mix_u64(self.#op as u64);
        }
    });
    let lookup_claim_mix_into_body = lookups.iter().map(|lookup| {
        quote! {
            channel.mix_u64(self.#lookup as u64);
        }
    });

    // Generate Claim::log_sizes() body
    let claim_log_sizes_body = opcodes.iter().map(|component| {
        let op = &component.name;
        let op_str = op.to_string();
        let pascal = to_pascal_case(&op_str);
        let columns_type = format_ident!("{}Columns", pascal);
        quote! {
            let count = air::trace::prover_columns::#columns_type::<()>::SIZE;
            sizes.extend(std::iter::repeat(self.#op).take(count));
        }
    });
    let lookup_claim_log_sizes_body = lookups.iter().map(|lookup| {
        quote! {
            sizes.push(self.#lookup);
        }
    });

    // Component-level claims are encoded once in the manifest. Keep their
    // positional representation generated from the same order used by
    // `Components::new`, `verifiers`, and the composition visitor.
    let component_count = opcodes.len() + lookups.len();
    let component_names = opcodes
        .iter()
        .map(|component| &component.name)
        .chain(lookups.iter());
    let claim_from_component_log_sizes = opcodes.iter().enumerate().map(|(index, component)| {
        let op = &component.name;
        quote! { #op: log_sizes[#index], }
    });
    let lookup_claim_from_component_log_sizes =
        lookups.iter().enumerate().map(|(lookup_index, lookup)| {
            let index = opcodes.len() + lookup_index;
            quote! { #lookup: log_sizes[#index], }
        });
    let claim_component_log_sizes = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! { self.#op, }
    });
    let lookup_claim_component_log_sizes = lookups.iter().map(|lookup| {
        quote! { self.#lookup, }
    });

    // Generate ClaimedSum fields
    let claimed_sum_fields = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! { pub #op: QM31, }
    });
    let lookup_claimed_sum_fields = lookups.iter().map(|lookup| {
        quote! { pub #lookup: QM31, }
    });

    // Generate ClaimedSum::sum() body
    let claimed_sum_body = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! { total += self.#op; }
    });
    let lookup_claimed_sum_body = lookups.iter().map(|lookup| {
        quote! {
            total += self.#lookup;
        }
    });

    // Generate ClaimedSum::mix_into() body
    let claimed_sum_mix_into = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! {
            channel.mix_felts(&[self.#op]);
        }
    });
    let lookup_claimed_sum_mix_into = lookups.iter().map(|lookup| {
        quote! {
            channel.mix_felts(&[self.#lookup]);
        }
    });
    let claimed_sum_from_component_values = opcodes.iter().enumerate().map(|(index, component)| {
        let op = &component.name;
        quote! { #op: values[#index], }
    });
    let lookup_claimed_sum_from_component_values =
        lookups.iter().enumerate().map(|(lookup_index, lookup)| {
            let index = opcodes.len() + lookup_index;
            quote! { #lookup: values[#index], }
        });
    let claimed_sum_component_values = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! { self.#op, }
    });
    let lookup_claimed_sum_component_values = lookups.iter().map(|lookup| {
        quote! { self.#lookup, }
    });

    // Generate Components struct fields
    let components_fields = opcodes.iter().map(|component| {
        let op = &component.name;
        let module = &component.module;
        quote! {
            pub #op: #module::air::Component,
        }
    });
    let lookup_components_fields = lookups.iter().map(|lookup| {
        quote! {
            pub #lookup: lookups::#lookup::air::Component,
        }
    });

    // Generate gen_trace() body
    let gen_trace_locals: Vec<_> = opcodes
        .iter()
        .map(|component| {
            let op = &component.name;
            quote! {
                let #op = tracer.#op.into_witness();
            }
        })
        .collect();
    let gen_trace_fields: Vec<_> = opcodes
        .iter()
        .map(|component| {
            let op = &component.name;
            quote! { #op, }
        })
        .collect();
    let gen_trace_counters_ref = quote! { &mut counters };

    let register_multiplicities_body: Vec<_> = opcodes
        .iter()
        .map(|component| {
            let op = &component.name;
            let module = &component.module;
            quote! {
                #module::witness::register_multiplicities(#op.as_slice(), #gen_trace_counters_ref);
            }
        })
        .collect();
    let lookup_gen_trace_fields = lookups.iter().map(|lookup| {
        quote! { #lookup: counters.#lookup.into_trace(), }
    });
    let fixed_trace_locals: Vec<_> = opcodes
        .iter()
        .enumerate()
        .map(|(index, component)| {
            let op = &component.name;
            let op_str = op.to_string();
            quote! {
                let rows = tracer.#op.len();
                let #op = tracer.#op
                    .into_witness_with_log_size(log_sizes[#index])
                    .ok_or(FixedTraceError::ComponentCapacityExceeded {
                        component: #op_str,
                        rows,
                        log_size: log_sizes[#index],
                    })?;
            }
        })
        .collect();
    let fixed_lookup_locals: Vec<_> = lookups
        .iter()
        .enumerate()
        .map(|(lookup_index, lookup)| {
            let index = opcodes.len() + lookup_index;
            let lookup_str = lookup.to_string();
            quote! {
                let #lookup = counters.#lookup.into_trace();
                let actual = #lookup
                    .first()
                    .map(|column| column.domain.log_size())
                    .unwrap_or(0);
                if actual != log_sizes[#index] {
                    return Err(FixedTraceError::LookupLogSizeMismatch {
                        component: #lookup_str,
                        expected: log_sizes[#index],
                        actual,
                    });
                }
            }
        })
        .collect();
    let fixed_lookup_fields = lookups.iter().map(|lookup| quote! { #lookup, });
    let gen_trace_function = quote! {
        pub fn gen_trace(
            tracer: air::trace::Tracer,
        ) -> Traces {
            let mut counters = crate::relations::Counters::new();
            #(#gen_trace_locals)*
            #(#register_multiplicities_body)*

            Traces {
                #(#gen_trace_fields)*
                #(#lookup_gen_trace_fields)*
            }
        }

        /// Generates execution traces at one verifier-owned component layout.
        pub fn gen_trace_at_log_sizes(
            tracer: air::trace::Tracer,
            log_sizes: [u32; COMPONENT_COUNT],
        ) -> Result<Traces, FixedTraceError> {
            let mut counters = crate::relations::Counters::new();
            #(#fixed_trace_locals)*
            #(#register_multiplicities_body)*
            #(#fixed_lookup_locals)*

            Ok(Traces {
                #(#gen_trace_fields)*
                #(#fixed_lookup_fields)*
            })
        }
    };

    // Generate gen_interaction_trace() body
    let gen_interaction_trace_vars = opcodes.iter().map(|component| {
        let op = &component.name;
        let module = &component.module;
        let claimed_var = format_ident!("{}_claimed", op);
        quote! {
            let (cols, claimed) = #module::witness::gen_interaction_trace(
                &traces.#op,
                relations,
            );
            all_columns.extend(cols);
            let #claimed_var = claimed;
        }
    });
    let lookup_interaction_trace = lookups.iter().map(|lookup| {
        let claimed_var = format_ident!("{}_claimed", lookup);
        quote! {
            let (cols, claimed) = lookups::#lookup::witness::gen_interaction_trace(
                &traces.#lookup,
                relations,
            );
            all_columns.extend(cols);
            let #claimed_var = claimed;
        }
    });

    let claimed_sum_inits = opcodes.iter().map(|component| {
        let op = &component.name;
        let claimed_var = format_ident!("{}_claimed", op);
        quote! {
            #op: #claimed_var,
        }
    });
    let lookup_claimed_sum_inits = lookups.iter().map(|lookup| {
        let claimed_var = format_ident!("{}_claimed", lookup);
        quote! { #lookup: #claimed_var, }
    });

    // Generate Components::new() body
    let components_new_body = opcodes.iter().map(|component| {
        let op = &component.name;
        let module = &component.module;
        quote! {
            #op: #module::air::Component::new(
                location_allocator,
                #module::air::Eval {
                    log_size: claim.#op,
                    relations: relations.clone(),
                },
                claimed_sum.#op,
            ),
        }
    });
    let lookup_components_new = lookups.iter().map(|lookup| {
        quote! {
            #lookup: lookups::#lookup::air::Component::new(
                location_allocator,
                lookups::#lookup::air::Eval {
                    log_size: claim.#lookup,
                    relations: relations.clone(),
                },
                claimed_sum.#lookup,
            ),
        }
    });

    // Generate Components::provers() body
    let provers_body = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! { &self.#op as &dyn stwo::prover::ComponentProver<SimdBackend>, }
    });
    let lookup_provers = lookups.iter().map(|lookup| {
        quote! { &self.#lookup as &dyn stwo::prover::ComponentProver<SimdBackend>, }
    });

    // Generate Components::verifiers() body
    let verifiers_body = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! { &self.#op as &dyn stwo::core::air::Component, }
    });
    // Visitor in the same order as verifiers(), so external consumers (the
    // recursion binding) iterate the composition exactly as the host does.
    let visit_body = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! { visitor.visit(&self.#op, claimed_sum.#op); }
    });
    let lookup_visit_body = lookups.iter().map(|lookup| {
        quote! { visitor.visit(&self.#lookup, claimed_sum.#lookup); }
    });
    let dynamic_visit_body = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! { visitor.visit(&self.#op, claimed_sum.#op); }
    });
    let dynamic_lookup_visit_body = lookups.iter().map(|lookup| {
        quote! { visitor.visit(&self.#lookup, claimed_sum.#lookup); }
    });
    let lookup_verifiers = lookups.iter().map(|lookup| {
        quote! { &self.#lookup as &dyn stwo::core::air::Component, }
    });

    // Generate relation_entries() body
    let relation_entries_body = if opcodes.is_empty() {
        quote! { std::iter::empty() }
    } else {
        let chain_items = opcodes.iter().map(|component| {
            let op = &component.name;
            quote! { add_to_relation_entries(&self.#op, trace) }
        });
        quote! {
            itertools::chain!(#(#chain_items),*)
        }
    };
    let lookup_relation_entries = lookups.iter().map(|lookup| {
        quote! { add_to_relation_entries(&self.#lookup, trace) }
    });

    // Generate trace_log_degree_bounds() body
    let trace_log_degree_bounds_body = opcodes.iter().map(|component| {
        let op = &component.name;
        quote! { self.#op.trace_log_degree_bounds(), }
    });
    let lookup_trace_log_degree_bounds = lookups.iter().map(|lookup| {
        quote! { self.#lookup.trace_log_degree_bounds(), }
    });

    // Generate assert_constraints_on_polys() body
    let assert_constraints_body = opcodes.iter().map(|component| {
        let op = &component.name;
        let module = &component.module;
        let op_str = op.to_string();
        quote! {
            if !traces.#op.is_empty() {
                let log_size = traces.#op.first()
                    .map(|t| t.domain.log_size())
                    .unwrap_or(0);
                if log_size > 0 {
                    let (interaction_trace, claimed_sum) =
                        #module::witness::gen_interaction_trace(&traces.#op, relations);
                    let trace_tree = TreeVec::new(vec![
                        vec![], // preprocessed
                        traces.#op.clone(),
                        interaction_trace,
                    ]);
                    let trace_polys = trace_tree.map_cols(|c| c.interpolate());
                    let eval = #module::air::Eval {
                        log_size,
                        relations: relations.clone(),
                    };
                    info!("Testing {} constraints (log_size={})", #op_str, log_size);
                    assert_constraints_on_polys(&trace_polys, CanonicCoset::new(log_size),
                        |assert_eval| { eval.evaluate(assert_eval); }, claimed_sum);
                    info!("{} constraints OK", #op_str);
                }
            }
        }
    });
    let lookup_assert_constraints = lookups.iter().map(|lookup| {
        let lookup_str = lookup.to_string();
        quote! {
            if !traces.#lookup.is_empty() {
                let log_size = traces.#lookup.first()
                    .map(|t| t.domain.log_size())
                    .unwrap_or(0);
                if log_size > 0 {
                    let (interaction_trace, claimed_sum) =
                        lookups::#lookup::witness::gen_interaction_trace(&traces.#lookup, relations);

                    let preprocessed_cols = crate::preprocessed::#lookup::Table::gen_columns();

                    let trace_tree = TreeVec::new(vec![
                        preprocessed_cols,
                        traces.#lookup.clone(),
                        interaction_trace,
                    ]);
                    let trace_polys = trace_tree.map_cols(|c| c.interpolate());
                    let eval = lookups::#lookup::air::Eval {
                        log_size,
                        relations: relations.clone(),
                    };
                    info!("Testing {} constraints (log_size={})", #lookup_str, log_size);
                    assert_constraints_on_polys(&trace_polys, CanonicCoset::new(log_size),
                        |assert_eval| { eval.evaluate(assert_eval); }, claimed_sum);
                    info!("{} constraints OK", #lookup_str);
                }
            }
        }
    });
    let track_relations_impl = quote! {
        pub fn track_relations(
            &self,
            preprocessed_trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
            traces: &Traces,
        ) -> stwo_constraint_framework::relation_tracker::RelationSummary {
            use stwo::core::pcs::TreeVec;
            use stwo::prover::backend::Column;

            let preprocessed_cpu: Vec<Vec<BaseField>> = preprocessed_trace
                .iter()
                .map(|col| col.values.to_cpu())
                .collect();
            let main_columns = traces.columns_cloned();
            let main_cpu: Vec<Vec<BaseField>> =
                main_columns.iter().map(|col| col.values.to_cpu()).collect();

            let cpu_trace = TreeVec::new(vec![preprocessed_cpu, main_cpu]);
            let trace_refs = TreeVec::new(
                cpu_trace.iter().map(|tree| tree.iter().collect()).collect(),
            );

            let entries = self.relation_entries(&trace_refs);
            stwo_constraint_framework::relation_tracker::RelationSummary::summarize_relations(
                &entries,
            )
            .cleaned()
        }
    };

    quote! {
        use serde::{Serialize, Deserialize};
        use stwo::core::fields::qm31::QM31;
        use stwo::core::fields::m31::BaseField;
        use stwo::core::ColumnVec;
        use stwo::core::air::Component as AirComponent;
        use stwo::prover::backend::simd::SimdBackend;
        use stwo::prover::poly::circle::CircleEvaluation;
        use stwo::prover::poly::BitReversedOrder;

        #[allow(dead_code)]
        fn assert_trace_table_coverage(tracer: air::trace::Tracer) {
            // The pattern has no `..` so every runner trace table must have a prover component entry.
            let air::trace::Tracer {
                clock: _,
                max_clock_diff: _,
                reg_clock: _,
                mem_clock: _,
                mem_initial: _,
                program_reads: _,
                #(#trace_table_coverage_fields)*
            } = tracer;
        }

        /// Trace columns for all components.
        pub struct Traces {
            #(#traces_fields)*
            #(#lookup_traces_fields)*
        }

        impl Traces {
            pub fn max_log_size(&self) -> u32 {
                self.log_sizes().into_iter().max().unwrap_or(4)
            }

            pub fn log_sizes(&self) -> Vec<u32> {
                let mut sizes = vec![];
                #(#log_sizes_body)*
                #(#lookup_log_sizes_body)*
                sizes
            }

            pub fn columns_cloned(&self) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
                let mut columns = vec![];
                #(#columns_cloned_body)*
                #(#lookup_columns_cloned_body)*
                columns
            }

            pub fn into_columns(self) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
                let mut columns = vec![];
                #(#into_columns_body)*
                #(#lookup_into_columns_body)*
                columns
            }

            pub fn print_tables(&self, max_rows: Option<usize>, max_cols: Option<usize>) {
                use debug_utils::ToTable;
                use stwo::prover::backend::Column;
                use crate::preprocessed::PreprocessedTable;
                debug_utils::set_display_options(max_rows, max_cols);
                #(#print_tables_body)*
                #(#lookup_print_tables_body)*
            }
        }

        #[derive(Debug, Clone, Serialize, Deserialize)]
        pub struct Claim {
            #(#claim_fields)*
            #(#lookup_claim_fields)*
        }

        /// Component order used by claims, claimed sums, and composition evaluation.
        pub const COMPONENT_COUNT: usize = #component_count;
        pub const COMPONENT_NAMES: [&str; COMPONENT_COUNT] = [
            #(stringify!(#component_names),)*
        ];

        /// A segment cannot enter a fixed proof profile with different table geometry.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum FixedTraceError {
            ComponentCapacityExceeded {
                component: &'static str,
                rows: usize,
                log_size: u32,
            },
            LookupLogSizeMismatch {
                component: &'static str,
                expected: u32,
                actual: u32,
            },
        }

        impl core::fmt::Display for FixedTraceError {
            fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                match self {
                    Self::ComponentCapacityExceeded { component, rows, log_size } => write!(
                        formatter,
                        "component {component} has {rows} rows, exceeding fixed log size {log_size}",
                    ),
                    Self::LookupLogSizeMismatch { component, expected, actual } => write!(
                        formatter,
                        "lookup component {component} has log size {actual}, expected {expected}",
                    ),
                }
            }
        }

        impl std::error::Error for FixedTraceError {}

        impl From<&Traces> for Claim {
            fn from(traces: &Traces) -> Self {
                Self {
                    #(#claim_from_body)*
                    #(#lookup_claim_from_body)*
                }
            }
        }

        impl Claim {
            pub fn from_component_log_sizes(log_sizes: [u32; COMPONENT_COUNT]) -> Self {
                Self {
                    #(#claim_from_component_log_sizes)*
                    #(#lookup_claim_from_component_log_sizes)*
                }
            }

            pub fn component_log_sizes(&self) -> [u32; COMPONENT_COUNT] {
                [
                    #(#claim_component_log_sizes)*
                    #(#lookup_claim_component_log_sizes)*
                ]
            }

            pub fn mix_into(&self, channel: &mut impl stwo::core::channel::Channel) {
                #(#claim_mix_into_body)*
                #(#lookup_claim_mix_into_body)*
            }

            pub fn log_sizes(&self) -> Vec<u32> {
                let mut sizes = vec![];
                #(#claim_log_sizes_body)*
                #(#lookup_claim_log_sizes_body)*
                sizes
            }

            pub fn main_trace_log_sizes(&self) -> Vec<u32> {
                self.log_sizes()
            }
        }

        /// Generic visitor over the typed components (the trait-object
        /// `verifiers()` cannot expose the generic `FrameworkEval`).
        pub trait ComponentVisitor {
            fn visit<E: stwo_constraint_framework::FrameworkEval>(
                &mut self,
                component: &stwo_constraint_framework::FrameworkComponent<E>,
                claimed_sum: QM31,
            );
        }

        /// Typed visitor for components that expose verifier-supplied relation coefficients.
        pub trait DynamicRelationComponentVisitor {
            fn visit<E>(&mut self, component: &stwo_constraint_framework::FrameworkComponent<E>, claimed_sum: QM31)
            where
                E: stwo_constraint_framework::FrameworkEval
                    + air::relation_eval::DynamicRelationFrameworkEval;
        }

        #[derive(Clone, Debug, Serialize, Deserialize)]
        pub struct ClaimedSum {
            #(#claimed_sum_fields)*
            #(#lookup_claimed_sum_fields)*
        }

        impl ClaimedSum {
            pub fn from_component_values(values: [QM31; COMPONENT_COUNT]) -> Self {
                Self {
                    #(#claimed_sum_from_component_values)*
                    #(#lookup_claimed_sum_from_component_values)*
                }
            }

            pub fn component_values(&self) -> [QM31; COMPONENT_COUNT] {
                [
                    #(#claimed_sum_component_values)*
                    #(#lookup_claimed_sum_component_values)*
                ]
            }

            pub fn sum(&self) -> QM31 {
                use num_traits::Zero;
                let mut total = QM31::zero();
                #(#claimed_sum_body)*
                #(#lookup_claimed_sum_body)*
                total
            }

            pub fn total(&self) -> QM31 {
                self.sum()
            }

            pub fn mix_into(&self, channel: &mut impl stwo::core::channel::Channel) {
                #(#claimed_sum_mix_into)*
                #(#lookup_claimed_sum_mix_into)*
            }
        }

        pub struct Components {
            #(#components_fields)*
            #(#lookup_components_fields)*
        }

        #gen_trace_function

        pub fn gen_interaction_trace(
            traces: &Traces,
            relations: &crate::relations::Relations,
        ) -> (
            ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
            ClaimedSum,
        ) {
            let mut all_columns = vec![];
            #(#gen_interaction_trace_vars)*
            #(#lookup_interaction_trace)*

            let claimed_sum = ClaimedSum {
                #(#claimed_sum_inits)*
                #(#lookup_claimed_sum_inits)*
            };

            (all_columns, claimed_sum)
        }

        impl Components {
            pub fn new(
                claim: &Claim,
                location_allocator: &mut stwo_constraint_framework::TraceLocationAllocator,
                relations: crate::relations::Relations,
                claimed_sum: &ClaimedSum,
            ) -> Self {
                Self {
                    #(#components_new_body)*
                    #(#lookup_components_new)*
                }
            }

            pub fn provers(&self) -> Vec<&dyn stwo::prover::ComponentProver<SimdBackend>> {
                vec![ #(#provers_body)* #(#lookup_provers)* ]
            }

            pub fn verifiers(&self) -> Vec<&dyn stwo::core::air::Component> {
                vec![ #(#verifiers_body)* #(#lookup_verifiers)* ]
            }

            /// Visit every component in composition (verifiers) order with
            /// its claimed sum.
            pub fn visit_components<V: ComponentVisitor>(
                &self,
                claimed_sum: &ClaimedSum,
                visitor: &mut V,
            ) {
                #(#visit_body)*
                #(#lookup_visit_body)*
            }

            /// Visit every component through its dynamic-relation evaluator in composition order.
            pub fn visit_dynamic_relation_components<V: DynamicRelationComponentVisitor>(
                &self,
                claimed_sum: &ClaimedSum,
                visitor: &mut V,
            ) {
                #(#dynamic_visit_body)*
                #(#dynamic_lookup_visit_body)*
            }

            pub fn relation_entries(
                &self,
                trace: &stwo::core::pcs::TreeVec<Vec<&Vec<BaseField>>>,
            ) -> Vec<stwo_constraint_framework::relation_tracker::RelationTrackerEntry> {
                use stwo_constraint_framework::relation_tracker::add_to_relation_entries;
                let mut entries: Vec<_> = #relation_entries_body.collect();
                #(entries.extend(#lookup_relation_entries);)*
                entries
            }

            pub fn trace_log_degree_bounds(&self) -> Vec<stwo::core::pcs::TreeVec<ColumnVec<u32>>> {
                vec![
                    #(#trace_log_degree_bounds_body)*
                    #(#lookup_trace_log_degree_bounds)*
                ]
            }

            pub fn assert_constraints_on_polys(
                traces: &Traces,
                relations: &crate::relations::Relations,
            ) {
                use stwo::core::pcs::TreeVec;
                use stwo::core::poly::circle::CanonicCoset;
                use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};
                use tracing::info;
                use crate::preprocessed::PreprocessedTable;

                #(#assert_constraints_body)*
                #(#lookup_assert_constraints)*
            }

            #track_relations_impl
        }
    }
}

fn render_lookup_components(tables: &[Ident]) -> TokenStream2 {
    // Lookup components are generated beside trace components because they prove counter-backed multiplicities.
    let inner_modules = tables.iter().map(|table| {
        quote! {
            pub mod #table {
                //! Lookup multiplicity component for a preprocessed table.

                pub mod air {
                    use air::relation_eval::{
                        DynamicRelationEvalAtRow, DynamicRelationFrameworkEval,
                    };
                    use stwo_constraint_framework::{
                        EvalAtRow, FrameworkComponent, FrameworkEval, RelationEntry,
                    };
                    use crate::preprocessed::PreprocessedTable;
                    use crate::relations::Relations;

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
                            let multiplicity = eval.next_trace_mask();
                            let column_ids = crate::preprocessed::#table::Table::column_ids();
                            let preprocessed_cols: Vec<E::F> = column_ids
                                .iter()
                                .map(|id| eval.get_preprocessed_column(id.clone()))
                                .collect();

                            // The lookup component emits the stored multiplicity so trace-backed consumers balance it.
                            eval.add_to_relation(RelationEntry::new(
                                &self.relations.#table,
                                -E::EF::from(multiplicity),
                                &preprocessed_cols,
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
                            let multiplicity = eval.next_trace_mask();
                            let column_ids = crate::preprocessed::#table::Table::column_ids();
                            let preprocessed_cols: Vec<E::F> = column_ids
                                .iter()
                                .map(|id| eval.get_preprocessed_column(id.clone()))
                                .collect();

                            eval.add_to_named_relation(
                                stringify!(#table),
                                -E::EF::from(multiplicity),
                                &preprocessed_cols,
                            );

                            eval.finalize_logup_in_pairs();
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
                    use stwo_constraint_framework::Relation;
                    use crate::preprocessed::PreprocessedTable;
                    use crate::relations::Relations;

                    pub fn gen_interaction_trace(
                        trace: &ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
                        relations: &Relations,
                    ) -> (
                        ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
                        QM31,
                    ) {
                        if trace.is_empty() {
                            return (vec![], QM31::zero());
                        }

                        let log_size = trace[0].domain.log_size();
                        let mut logup_gen = LogupTraceGenerator::new(log_size);
                        let preprocessed_cols = crate::preprocessed::#table::Table::gen_columns();
                        let multiplicity = &trace[0].values.data;

                        // The interaction trace uses the relation sign that balances trace-backed lookup consumers.
                        let multiplicity_qm31: Vec<PackedQM31> = multiplicity
                            .iter()
                            .map(|&m| -PackedQM31::from(m))
                            .collect();

                        let col_data: Vec<&[stwo::prover::backend::simd::m31::PackedM31]> =
                            preprocessed_cols.iter().map(|c| c.values.data.as_slice()).collect();

                        let simd_size = col_data[0].len();
                        let mut denom: Vec<PackedQM31> = Vec::with_capacity(simd_size);
                        for row in 0..simd_size {
                            let packed_m31_values: Vec<stwo::prover::backend::simd::m31::PackedM31> =
                                col_data.iter().map(|c| c[row]).collect();
                            denom.push(relations.#table.combine(&packed_m31_values));
                        }

                        // Write multiplicity / denom fraction
                        stwo_macros::write_col!(&multiplicity_qm31, &denom, logup_gen);

                        logup_gen.finalize_last()
                    }
                }
            }
        }
    });

    quote! {
        #(#inner_modules)*
    }
}
