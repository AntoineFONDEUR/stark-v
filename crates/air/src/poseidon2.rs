//! Poseidon2 over M31: the plain permutation (channel and Merkle hashing)
//! and the felt-compiled AIR table (see the `define_air_fns!` invocation
//! below — table, columns, constraints, and row fill from one definition).

// clippy's array-comma heuristic misfires inside the macro expansion.
#![allow(clippy::possible_missing_comma)]

use stwo::core::fields::m31::M31;

pub const T: usize = 16;
pub const DIGEST_WORDS: usize = T / 2;
pub const FULL_ROUNDS: usize = 8;
pub const PARTIAL_ROUNDS: usize = 14;

/// Full-width digest used by Poseidon2 Merkle trees.
pub type Poseidon2Digest = [u32; DIGEST_WORDS];

pub const EXTERNAL_ROUND_CONSTS: [[u32; 16]; 8] = [
    [
        1988864850, 1893772157, 1025928330, 1839472709, 1611656994, 1104858731, 1694088660,
        1564660990, 1991332205, 1875486487, 1890340790, 1658614, 582370530, 528029397, 1196956642,
        655401251,
    ],
    [
        1652877415, 26032894, 1576640243, 1277052539, 1450142396, 697623591, 1401580866,
        1568404175, 2145004971, 265835716, 1183985610, 1031234465, 436012490, 172735299, 352802897,
        1032863094,
    ],
    [
        757665783, 1082171296, 1507509996, 309929890, 1807683232, 43258895, 611592566, 1854193793,
        575164234, 894217817, 72613857, 1061659596, 8921166, 1617355017, 998001536, 1800758877,
    ],
    [
        1002748055, 1935405944, 1351462722, 411368491, 1913975372, 1956167178, 442558016,
        855898408, 699687798, 1553382248, 1708169125, 490049183, 1251643415, 1193594742, 880473871,
        511174042,
    ],
    [
        1460209171, 530850056, 398192464, 536338716, 75179210, 1309934197, 1335920373, 127611036,
        291093831, 1832379621, 123571662, 303176864, 2137685056, 1759609530, 1418928155, 71608334,
    ],
    [
        6616262, 1684515814, 1721194338, 720801691, 878392254, 460379263, 87930647, 940673483,
        1136203256, 551499412, 256220454, 2007034235, 796124985, 410436345, 1705042586, 1286336446,
    ],
    [
        1522340456, 1295296352, 309794713, 1772145068, 956898901, 2137070800, 988829146,
        2059451359, 1846491684, 1105442551, 1236497773, 1452000568, 549485016, 385992492,
        1987107948, 1514377269,
    ],
    [
        2090065934, 1444920141, 293113979, 41120774, 855319793, 1663284746, 1789994008, 1120509162,
        358222743, 1406256810, 735183687, 664485235, 1331641456, 38121324, 595810771, 1234594393,
    ],
];

pub const INTERNAL_ROUND_CONSTS: [u32; 14] = [
    2139014335, 69309039, 1368974953, 886780232, 1130937085, 1718115455, 2027103386, 1612216449,
    1994053242, 110146615, 514413329, 1088763546, 955319292, 488794657,
];

pub const INTERNAL_MATRIX: [u32; 16] = [
    129501892, 1809435443, 1223573407, 1331944729, 415581875, 1526242955, 1341275624, 1333308150,
    1404946132, 1549369918, 709303410, 1284988537, 1490838740, 115945821, 754131590, 800486749,
];

#[inline]
fn add_m31(a: u32, b: u32) -> u32 {
    (M31::from(a) + M31::from(b)).0
}

#[inline]
fn mul_m31(a: u32, b: u32) -> u32 {
    (M31::from(a) * M31::from(b)).0
}

#[inline]
fn square_m31(x: u32) -> u32 {
    (M31::from(x) * M31::from(x)).0
}

#[inline]
fn apply_m4(x: [u32; 4]) -> [u32; 4] {
    let t0 = add_m31(x[0], x[1]);
    let t02 = add_m31(t0, t0);
    let t1 = add_m31(x[2], x[3]);
    let t12 = add_m31(t1, t1);
    let t2 = add_m31(add_m31(x[1], x[1]), t1);
    let t3 = add_m31(add_m31(x[3], x[3]), t0);
    let t4 = add_m31(add_m31(t12, t12), t3);
    let t5 = add_m31(add_m31(t02, t02), t2);
    let t6 = add_m31(t3, t5);
    let t7 = add_m31(t2, t4);
    [t6, t5, t7, t4]
}

#[inline]
fn apply_external_round_matrix(state: &mut [u32; 16]) {
    for i in 0..4 {
        let base = 4 * i;
        let out = apply_m4([
            state[base],
            state[base + 1],
            state[base + 2],
            state[base + 3],
        ]);
        state[base] = out[0];
        state[base + 1] = out[1];
        state[base + 2] = out[2];
        state[base + 3] = out[3];
    }

    for j in 0..4 {
        let mut sum = 0u32;
        sum = add_m31(sum, state[j]);
        sum = add_m31(sum, state[j + 4]);
        sum = add_m31(sum, state[j + 8]);
        sum = add_m31(sum, state[j + 12]);
        for i in 0..4 {
            let idx = 4 * i + j;
            state[idx] = add_m31(state[idx], sum);
        }
    }
}

#[inline]
fn apply_internal_round_matrix(state: &mut [u32; 16]) {
    let mut sum = 0u32;
    for val in state.iter() {
        sum = add_m31(sum, *val);
    }

    for (state_i, matrix_i) in state.iter_mut().zip(INTERNAL_MATRIX.iter()) {
        *state_i = add_m31(mul_m31(*state_i, *matrix_i), sum);
    }
}

/// The plain Poseidon2 permutation over `[M31; 16]`, without trace recording.
///
/// Same rounds, constants, and matrices as [`poseidon2_traced_state`]; used by the
/// proof-system channel and Merkle hasher where no AIR trace is needed.
pub fn poseidon2_permutation(state: &mut [u32; T]) {
    apply_external_round_matrix(state);

    for round_consts in EXTERNAL_ROUND_CONSTS.iter().take(FULL_ROUNDS / 2) {
        for (state_i, round_const) in state.iter_mut().zip(round_consts.iter()) {
            *state_i = add_m31(*state_i, *round_const);
        }
        let initial_state = *state;
        for state_i in state.iter_mut() {
            *state_i = square_m31(square_m31(*state_i));
        }
        for (state_i, init_i) in state.iter_mut().zip(initial_state.iter()) {
            *state_i = mul_m31(*state_i, *init_i);
        }
        apply_external_round_matrix(state);
    }

    for round_const in INTERNAL_ROUND_CONSTS.iter() {
        state[0] = add_m31(state[0], *round_const);
        let initial_state = state[0];
        state[0] = mul_m31(square_m31(square_m31(state[0])), initial_state);
        apply_internal_round_matrix(state);
    }

    for round_consts in EXTERNAL_ROUND_CONSTS.iter().skip(FULL_ROUNDS / 2) {
        for (state_i, round_const) in state.iter_mut().zip(round_consts.iter()) {
            *state_i = add_m31(*state_i, *round_const);
        }
        let initial_state = *state;
        for state_i in state.iter_mut() {
            *state_i = square_m31(square_m31(*state_i));
        }
        for (state_i, init_i) in state.iter_mut().zip(initial_state.iter()) {
            *state_i = mul_m31(*state_i, *init_i);
        }
        apply_external_round_matrix(state);
    }
}

/// Hash two full-width child digests and return the complete permutation output.
pub fn poseidon2_hash(left: Poseidon2Digest, right: Poseidon2Digest) -> [u32; T] {
    let mut state = [0; T];
    state[..DIGEST_WORDS].copy_from_slice(&left);
    state[DIGEST_WORDS..].copy_from_slice(&right);
    poseidon2_permutation(&mut state);
    state
}

/// Full-width digest of two Merkle children.
pub fn poseidon2_hash_digest(left: Poseidon2Digest, right: Poseidon2Digest) -> Poseidon2Digest {
    poseidon2_hash(left, right)[..DIGEST_WORDS]
        .try_into()
        .expect("digest width is half the permutation state")
}

/// Default digests by depth for the M31-addressed sparse Merkle tree.
///
/// The array index is the Merkle depth; the final entry is the all-zero leaf.
pub fn poseidon2_default_hashes() -> [Poseidon2Digest; crate::MAX_TREE_HEIGHT as usize] {
    let mut defaults = [[0; DIGEST_WORDS]; crate::MAX_TREE_HEIGHT as usize];
    for depth in (0..defaults.len() - 1).rev() {
        defaults[depth] = poseidon2_hash_digest(defaults[depth + 1], defaults[depth + 1]);
    }
    defaults
}

// The Poseidon2 permutation as a felt function: the table, the columns
// struct with its straight-line `evaluation()` (constraints and the
// `(input, output)` activation tuple), and the row fill all derive from
// this one definition. The `wide`/`io` flag columns select the digest
// emission shape in the prover component.
stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [wide, io],
    embedded_component: true,

    // The 4x4 MDS block of the external round matrix, as its addition chain.
    inline fn m4(x0, x1, x2, x3) {
        let t0 = x0 + x1;
        let t1 = x2 + x3;
        let t2 = 2 * x1 + t1;
        let t3 = 2 * x3 + t0;
        let t4 = 4 * t1 + t3;
        let t5 = 4 * t0 + t2;
        let t6 = t3 + t5;
        let t7 = t2 + t4;
        return (t6, t5, t7, t4);
    }

    // External round matrix: M4 per 4-lane block, then each lane adds its
    // column-wise sum across the blocks. Purely additive: stays inline.
    inline fn external_matrix(state: [felt; 16]) {
        let (b0, b1, b2, b3) = m4(state[0], state[1], state[2], state[3]);
        let (b4, b5, b6, b7) = m4(state[4], state[5], state[6], state[7]);
        let (b8, b9, b10, b11) = m4(state[8], state[9], state[10], state[11]);
        let (b12, b13, b14, b15) = m4(state[12], state[13], state[14], state[15]);
        let mixed = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15];
        let sums = map(j, 0..4, mixed[j] + mixed[j + 4] + mixed[j + 8] + mixed[j + 12]);
        let out = map(k, 0..16, mixed[k] + sums[k % 4]);
        return out;
    }

    // 4 + 4 full rounds around 14 partial rounds; the x^5 s-box chains
    // materialize automatically under the degree budget.
    fn poseidon2(state: [felt; 16]) {
        let state = external_matrix(state);
        for r in 0..4 {
            let state = map(j, 0..16, (state[j] + constant(EXTERNAL_ROUND_CONSTS[r][j])) ** 5);
            let state = external_matrix(state);
        }
        for r in 0..14 {
            let state = update(state, 0, (state[0] + constant(INTERNAL_ROUND_CONSTS[r])) ** 5);
            let total = sum(j, 0..16, state[j]);
            let state = map(j, 0..16, state[j] * constant(INTERNAL_MATRIX[j]) + total);
        }
        for r in 4..8 {
            let state = map(j, 0..16, (state[j] + constant(EXTERNAL_ROUND_CONSTS[r][j])) ** 5);
            let state = external_matrix(state);
        }
        return state;
    }
}

/// Trace one permutation of an arbitrary initial state into the table and
/// return the output state.
///
/// `wide` selects the 8-word digest emission in the Poseidon2 component
/// (proof commitment trees) instead of the 1-word one (memory trees); `io`
/// selects the atomic (input, output) pair emission for sponge chaining.
pub fn poseidon2_traced_state(
    table: &mut Poseidon2Table,
    initial_state: [u32; T],
    wide: bool,
    io: bool,
) -> [u32; T] {
    let outputs = poseidon2_fill(
        table,
        initial_state.map(M31::from),
        [wide as u32, io as u32],
    );
    outputs.map(|v| v.0)
}

/// Trace one full-width Merkle hash as an atomic input/output permutation call.
pub fn poseidon2_traced_digest(
    table: &mut Poseidon2Table,
    left: Poseidon2Digest,
    right: Poseidon2Digest,
) -> [u32; T] {
    let mut state = [0; T];
    state[..DIGEST_WORDS].copy_from_slice(&left);
    state[DIGEST_WORDS..].copy_from_slice(&right);
    poseidon2_traced_state(table, state, false, true)
}

#[cfg(test)]
mod permutation_tests {
    use super::*;

    #[test]
    fn test_fill_matches_permutation() {
        // The felt-compiled fill and the plain permutation are the same
        // rounds, constants, and matrices.
        let mut table = Poseidon2Table::new();
        let state: [u32; T] = core::array::from_fn(|i| 123456789 + i as u32);
        let traced = poseidon2_traced_state(&mut table, state, false, false);
        let mut expected = state;
        poseidon2_permutation(&mut expected);
        assert_eq!(traced, expected);
    }

    #[test]
    fn test_default_hashes_match_permutation_chain() {
        // Each depth's default digest is the permutation of two copies of the
        // depth below, anchored at the zero leaf.
        let actual = poseidon2_default_hashes();
        let mut expected = [[0; DIGEST_WORDS]; crate::MAX_TREE_HEIGHT as usize];
        for depth in (0..expected.len() - 1).rev() {
            let child = expected[depth + 1];
            expected[depth] = poseidon2_hash(child, child)[..DIGEST_WORDS]
                .try_into()
                .expect("digest width");
        }
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_traced_digest_matches_plain_full_output() {
        let left = core::array::from_fn(|index| 100 + index as u32);
        let right = core::array::from_fn(|index| 200 + index as u32);
        let mut table = Poseidon2Table::new();
        assert_eq!(
            poseidon2_traced_digest(&mut table, left, right),
            poseidon2_hash(left, right)
        );
    }
}
