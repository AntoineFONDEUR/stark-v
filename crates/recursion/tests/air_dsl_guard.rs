//! Structural enforcement for every AIR source reachable from recursion.
//!
//! The universal proof roster and the inner VM proof roster are fixed here
//! together with their source owners. Parsing those owners as Rust syntax keeps
//! handwritten evaluators, standalone table macros, and wrapper macros from
//! re-entering either recursive branch.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use recursion::recursion_air_program::UNIVERSAL_COMPONENT_NAMES;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{Item, ItemMacro, Path as SynPath, Token, braced};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ComponentOwner {
    name: &'static str,
    source: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct OwnerPolicy {
    source: &'static str,
    accepted_macro_count: usize,
}

#[derive(Debug, Default, PartialEq, Eq)]
struct SourceInspection {
    accepted_macro_count: usize,
    framework_eval_impls: Vec<String>,
    standalone_table_macro_count: usize,
    wrapper_macro_count: usize,
    unexpected_item_macros: Vec<String>,
}

const UNIVERSAL_INVENTORY: [ComponentOwner; 36] = [
    ComponentOwner {
        name: "control",
        source: "crates/recursion/src/control_air.rs",
    },
    ComponentOwner {
        name: "transcript_air",
        source: "crates/recursion/src/transcript_air.rs",
    },
    ComponentOwner {
        name: "transcript_binding",
        source: "crates/recursion/src/transcript_binding_air.rs",
    },
    ComponentOwner {
        name: "transcript_state",
        source: "crates/recursion/src/transcript_state_air.rs",
    },
    ComponentOwner {
        name: "transcript_word",
        source: "crates/recursion/src/transcript_word_air.rs",
    },
    ComponentOwner {
        name: "transcript_payload",
        source: "crates/recursion/src/transcript_payload_air.rs",
    },
    ComponentOwner {
        name: "pow_check",
        source: "crates/recursion/src/pow.rs",
    },
    ComponentOwner {
        name: "pow_frame",
        source: "crates/recursion/src/pow.rs",
    },
    ComponentOwner {
        name: "relation_challenge",
        source: "crates/recursion/src/relation_challenge_air.rs",
    },
    ComponentOwner {
        name: "verifier_randomness",
        source: "crates/recursion/src/verifier_randomness_air.rs",
    },
    ComponentOwner {
        name: "statement_input",
        source: "crates/recursion/src/statement_input_air.rs",
    },
    ComponentOwner {
        name: "statement_semantics_input",
        source: "crates/recursion/src/statement_semantics_input_air.rs",
    },
    ComponentOwner {
        name: "vm_public_claim_input",
        source: "crates/recursion/src/vm_public_claim_input_air.rs",
    },
    ComponentOwner {
        name: "vm_public_claim_hash",
        source: "crates/recursion/src/vm_public_claim_hash_air.rs",
    },
    ComponentOwner {
        name: "vm_public_io_hash",
        source: "crates/recursion/src/vm_public_io_hash_air.rs",
    },
    ComponentOwner {
        name: "vm_public_claim_semantics_input",
        source: "crates/recursion/src/vm_public_claim_semantics_input_air.rs",
    },
    ComponentOwner {
        name: "vm_public_logup_input",
        source: "crates/recursion/src/vm_public_logup_input_air.rs",
    },
    ComponentOwner {
        name: "vm_public_logup_control",
        source: "crates/recursion/src/vm_public_logup_control_air.rs",
    },
    ComponentOwner {
        name: "vm_air_composition_input",
        source: "crates/recursion/src/vm_air_composition_input_air.rs",
    },
    ComponentOwner {
        name: "vm_air_composition_control",
        source: "crates/recursion/src/vm_air_composition_control_air.rs",
    },
    ComponentOwner {
        name: "query_bits",
        source: "crates/recursion/src/query_position_air.rs",
    },
    ComponentOwner {
        name: "query_mapping",
        source: "crates/recursion/src/query_position_air.rs",
    },
    ComponentOwner {
        name: "merkle_root",
        source: "crates/recursion/src/merkle_root_air.rs",
    },
    ComponentOwner {
        name: "trace_merkle",
        source: "crates/recursion/src/trace_merkle_air.rs",
    },
    ComponentOwner {
        name: "pcs_deep_input",
        source: "crates/recursion/src/pcs_deep_input_air.rs",
    },
    ComponentOwner {
        name: "fri_merkle_leaf",
        source: "crates/recursion/src/fri_merkle_air.rs",
    },
    ComponentOwner {
        name: "fri_merkle_node",
        source: "crates/recursion/src/fri_merkle_air.rs",
    },
    ComponentOwner {
        name: "fri_merkle_anchor",
        source: "crates/recursion/src/fri_merkle_air.rs",
    },
    ComponentOwner {
        name: "fri_verifier_control",
        source: "crates/recursion/src/fri_verifier_control_air.rs",
    },
    ComponentOwner {
        name: "fri_verifier_input",
        source: "crates/recursion/src/fri_verifier_input_air.rs",
    },
    ComponentOwner {
        name: "qm31_mul",
        source: "crates/recursion/src/qm31_mul.rs",
    },
    ComponentOwner {
        name: "qm31_inv",
        source: "crates/recursion/src/qm31_inv.rs",
    },
    ComponentOwner {
        name: "linear_ops",
        source: "crates/recursion/src/linear_ops.rs",
    },
    ComponentOwner {
        name: "merkle_path",
        source: "crates/recursion/src/merkle_path.rs",
    },
    ComponentOwner {
        name: "poseidon2",
        source: "crates/air/src/poseidon2.rs",
    },
    ComponentOwner {
        name: "range_check_8_8",
        source: "crates/air/src/schema.rs",
    },
];

const VM_INVENTORY: [ComponentOwner; 27] = [
    ComponentOwner {
        name: "auipc",
        source: "crates/air/src/opcodes/auipc.rs",
    },
    ComponentOwner {
        name: "base_alu_imm",
        source: "crates/air/src/opcodes/base_alu_imm.rs",
    },
    ComponentOwner {
        name: "base_alu_reg",
        source: "crates/air/src/opcodes/base_alu_reg.rs",
    },
    ComponentOwner {
        name: "branch_eq",
        source: "crates/air/src/opcodes/branch_eq.rs",
    },
    ComponentOwner {
        name: "branch_lt",
        source: "crates/air/src/opcodes/branch_lt.rs",
    },
    ComponentOwner {
        name: "commit",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "div",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "jal",
        source: "crates/air/src/opcodes/jal.rs",
    },
    ComponentOwner {
        name: "jalr",
        source: "crates/air/src/opcodes/jalr.rs",
    },
    ComponentOwner {
        name: "load_store",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "lt_imm",
        source: "crates/air/src/opcodes/lt_imm.rs",
    },
    ComponentOwner {
        name: "lt_reg",
        source: "crates/air/src/opcodes/lt_reg.rs",
    },
    ComponentOwner {
        name: "lui",
        source: "crates/air/src/opcodes/lui.rs",
    },
    ComponentOwner {
        name: "mul",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "mulh",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "shifts_imm",
        source: "crates/air/src/opcodes/shifts_imm.rs",
    },
    ComponentOwner {
        name: "shifts_reg",
        source: "crates/air/src/opcodes/shifts_reg.rs",
    },
    ComponentOwner {
        name: "program",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "memory",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "merkle",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "clock_update",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "bitwise",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "range_check_20",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "range_check_8_11",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "range_check_8_8_4",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "range_check_8_8",
        source: "crates/air/src/schema.rs",
    },
    ComponentOwner {
        name: "range_check_m31",
        source: "crates/air/src/schema.rs",
    },
];

const OWNER_POLICIES: [OwnerPolicy; 44] = [
    OwnerPolicy {
        source: "crates/air/src/opcodes/auipc.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/opcodes/base_alu_imm.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/opcodes/base_alu_reg.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/opcodes/branch_eq.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/opcodes/branch_lt.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/opcodes/jal.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/opcodes/jalr.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/opcodes/lt_imm.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/opcodes/lt_reg.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/opcodes/lui.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/opcodes/shifts_imm.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/opcodes/shifts_reg.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/poseidon2.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/air/src/schema.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/control_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/fri_merkle_air.rs",
        accepted_macro_count: 3,
    },
    OwnerPolicy {
        source: "crates/recursion/src/fri_verifier_control_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/fri_verifier_input_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/linear_ops.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/merkle_path.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/merkle_root_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/pcs_deep_input_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/pow.rs",
        accepted_macro_count: 2,
    },
    OwnerPolicy {
        source: "crates/recursion/src/qm31_inv.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/qm31_mul.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/query_position_air.rs",
        accepted_macro_count: 2,
    },
    OwnerPolicy {
        source: "crates/recursion/src/relation_challenge_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/statement_input_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/statement_semantics_input_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/trace_merkle_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/transcript_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/transcript_binding_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/transcript_payload_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/transcript_state_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/transcript_word_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/verifier_randomness_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/vm_air_composition_control_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/vm_air_composition_input_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/vm_public_claim_hash_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/vm_public_claim_input_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/vm_public_claim_semantics_input_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/vm_public_io_hash_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/vm_public_logup_control_air.rs",
        accepted_macro_count: 1,
    },
    OwnerPolicy {
        source: "crates/recursion/src/vm_public_logup_input_air.rs",
        accepted_macro_count: 1,
    },
];

#[test]
fn universal_roster_matches_the_checked_in_air_inventory() {
    assert_eq!(
        UNIVERSAL_COMPONENT_NAMES,
        UNIVERSAL_INVENTORY.map(|component| component.name)
    );
}

#[test]
fn vm_roster_matches_the_checked_in_air_inventory() {
    assert_eq!(
        prover::components::COMPONENT_NAMES,
        VM_INVENTORY.map(|component| component.name)
    );
}

#[test]
fn every_inventory_owner_has_a_structural_policy() {
    let inventoried = UNIVERSAL_INVENTORY
        .iter()
        .chain(&VM_INVENTORY)
        .map(|component| component.source)
        .collect::<BTreeSet<_>>();
    let guarded = OWNER_POLICIES
        .iter()
        .map(|policy| policy.source)
        .collect::<BTreeSet<_>>();
    assert_eq!(guarded, inventoried);
}

#[test]
fn every_reachable_air_owner_uses_only_the_direct_dsl() {
    let violations = OWNER_POLICIES
        .iter()
        .filter_map(|policy| {
            let inspection = inspect_source(policy.source);
            let expected = SourceInspection {
                accepted_macro_count: policy.accepted_macro_count,
                ..SourceInspection::default()
            };
            (inspection != expected).then_some((policy.source, expected, inspection))
        })
        .collect::<Vec<_>>();
    assert!(violations.is_empty(), "invalid AIR owners: {violations:#?}");
}

#[test]
fn vm_component_router_uses_only_the_expected_dsl_routes() {
    let (custom_routes, detached) = parse_vm_component_router();
    assert_eq!(
        (custom_routes, detached),
        (
            vec![
                (
                    "auipc".to_owned(),
                    "air::opcodes::auipc::component".to_owned(),
                ),
                (
                    "base_alu_imm".to_owned(),
                    "air::opcodes::base_alu_imm::component".to_owned(),
                ),
                (
                    "base_alu_reg".to_owned(),
                    "air::opcodes::base_alu_reg::component".to_owned(),
                ),
                (
                    "branch_eq".to_owned(),
                    "air::opcodes::branch_eq::component".to_owned(),
                ),
                (
                    "branch_lt".to_owned(),
                    "air::opcodes::branch_lt::component".to_owned(),
                ),
                ("jal".to_owned(), "air::opcodes::jal::component".to_owned(),),
                (
                    "jalr".to_owned(),
                    "air::opcodes::jalr::component".to_owned(),
                ),
                (
                    "lt_imm".to_owned(),
                    "air::opcodes::lt_imm::component".to_owned(),
                ),
                (
                    "lt_reg".to_owned(),
                    "air::opcodes::lt_reg::component".to_owned(),
                ),
                ("lui".to_owned(), "air::opcodes::lui::component".to_owned()),
                (
                    "shifts_imm".to_owned(),
                    "air::opcodes::shifts_imm::component".to_owned(),
                ),
                (
                    "shifts_reg".to_owned(),
                    "air::opcodes::shifts_reg::component".to_owned(),
                ),
            ],
            vec!["poseidon2".to_owned()],
        )
    );
}

fn workspace_root() -> PathBuf {
    // Cargo exposes the crate location on every machine, so no checkout path
    // enters the guard or its diagnostics.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn inspect_source(relative_path: &str) -> SourceInspection {
    let path = workspace_root().join(relative_path);
    let source = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    let syntax = syn::parse_file(&source)
        .unwrap_or_else(|error| panic!("failed to parse {}: {error}", path.display()));
    let mut inspection = SourceInspection::default();
    inspect_items(&syntax.items, &mut inspection);
    inspection
}

fn inspect_items(items: &[Item], inspection: &mut SourceInspection) {
    for item in items {
        match item {
            Item::Impl(item_impl) => {
                if item_impl
                    .trait_
                    .as_ref()
                    .and_then(|(_, path, _)| path.segments.last())
                    .is_some_and(|segment| segment.ident == "FrameworkEval")
                {
                    inspection
                        .framework_eval_impls
                        .push(match item_impl.self_ty.as_ref() {
                            syn::Type::Path(path) => path
                                .path
                                .segments
                                .iter()
                                .map(|segment| segment.ident.to_string())
                                .collect::<Vec<_>>()
                                .join("::"),
                            _ => "<non-path evaluator type>".to_owned(),
                        });
                }
            }
            Item::Macro(item_macro) => inspect_macro(item_macro, inspection),
            Item::Mod(item_mod) => {
                if let Some((_, nested)) = &item_mod.content {
                    inspect_items(nested, inspection);
                }
            }
            _ => {}
        }
    }
}

fn inspect_macro(item_macro: &ItemMacro, inspection: &mut SourceInspection) {
    let Some(name) = item_macro
        .mac
        .path
        .segments
        .last()
        .map(|segment| &segment.ident)
    else {
        return;
    };
    match name.to_string().as_str() {
        "define_air" | "define_air_fns" => inspection.accepted_macro_count += 1,
        // Relation declarations define lookup types, not AIR components.
        "relation" => {}
        "define_component_tables" => inspection.standalone_table_macro_count += 1,
        "macro_rules" => inspection.wrapper_macro_count += 1,
        _ => inspection.unexpected_item_macros.push(name.to_string()),
    }
}

struct RouterEntry {
    name: syn::Ident,
    custom_module: Option<SynPath>,
}

impl Parse for RouterEntry {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let source: SynPath = input.parse()?;
        let name = source
            .segments
            .last()
            .expect("component paths have a final segment")
            .ident
            .clone();
        let custom_module = if input.peek(Token![:]) {
            input.parse::<Token![:]>()?;
            Some(input.parse()?)
        } else {
            None
        };
        Ok(Self {
            name,
            custom_module,
        })
    }
}

struct ComponentRouter {
    trace: Vec<RouterEntry>,
    detached: Vec<syn::Ident>,
}

impl Parse for ComponentRouter {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let trace_label: syn::Ident = input.parse()?;
        if trace_label != "trace" {
            return Err(syn::Error::new(
                trace_label.span(),
                "expected trace section",
            ));
        }
        input.parse::<Token![:]>()?;
        let trace_content;
        braced!(trace_content in input);
        let trace = Punctuated::<RouterEntry, Token![,]>::parse_terminated(&trace_content)?
            .into_iter()
            .collect();
        input.parse::<Token![,]>()?;
        let next_label: syn::Ident = input.parse()?;
        let (detached, lookup_label) = if next_label == "detached" {
            input.parse::<Token![:]>()?;
            let detached_content;
            braced!(detached_content in input);
            let detached =
                Punctuated::<syn::Ident, Token![,]>::parse_terminated(&detached_content)?
                    .into_iter()
                    .collect();
            input.parse::<Token![,]>()?;
            (detached, input.parse()?)
        } else {
            (vec![], next_label)
        };
        if lookup_label != "lookup" {
            return Err(syn::Error::new(
                lookup_label.span(),
                "expected lookup section",
            ));
        }
        input.parse::<Token![:]>()?;
        let lookup_content;
        braced!(lookup_content in input);
        let _ = Punctuated::<syn::Ident, Token![,]>::parse_terminated(&lookup_content)?;
        let _ = input.parse::<Token![,]>();
        Ok(Self { trace, detached })
    }
}

fn parse_vm_component_router() -> (Vec<(String, String)>, Vec<String>) {
    let path = workspace_root().join("crates/prover/src/components/mod.rs");
    let source = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
    let syntax = syn::parse_file(&source)
        .unwrap_or_else(|error| panic!("failed to parse {}: {error}", path.display()));
    let router = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Macro(item_macro)
                if item_macro
                    .mac
                    .path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.ident == "components") =>
            {
                Some(syn::parse2::<ComponentRouter>(
                    item_macro.mac.tokens.clone(),
                ))
            }
            _ => None,
        })
        .next()
        .expect("the prover declares one components router")
        .expect("the prover components router has the expected structure");
    let custom_routes = router
        .trace
        .into_iter()
        .filter_map(|entry| {
            entry.custom_module.map(|path| {
                let path = path
                    .segments
                    .iter()
                    .map(|segment| segment.ident.to_string())
                    .collect::<Vec<_>>()
                    .join("::");
                (entry.name.to_string(), path)
            })
        })
        .collect();
    let detached = router
        .detached
        .into_iter()
        .map(|name| name.to_string())
        .collect();
    (custom_routes, detached)
}
