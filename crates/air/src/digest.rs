//! Canonical M31 words and full-width digests shared by AIR-facing protocols.
//!
//! Raw `u32` values can equal or exceed the M31 modulus. `M31Word` rejects
//! those aliases once at the input boundary, so digest consumers can treat
//! every stored limb as the unique integer representative of a field element.

use core::fmt;

use stwo::core::fields::m31::{M31, P};

/// A `u32` whose value is the canonical representative of an M31 element.
#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct M31Word(u32);

impl M31Word {
    /// The additive identity in canonical word form.
    pub const ZERO: Self = Self(0);

    /// Returns the canonical integer representative.
    pub const fn as_u32(self) -> u32 {
        self.0
    }
}

impl From<u16> for M31Word {
    fn from(value: u16) -> Self {
        Self(u32::from(value))
    }
}

impl From<M31> for M31Word {
    fn from(value: M31) -> Self {
        Self(value.0)
    }
}

impl From<M31Word> for M31 {
    fn from(value: M31Word) -> Self {
        M31::from_u32_unchecked(value.0)
    }
}

impl TryFrom<u32> for M31Word {
    type Error = NonCanonicalM31Word;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        if value < P {
            Ok(Self(value))
        } else {
            Err(NonCanonicalM31Word { value })
        }
    }
}

/// A raw word that is not the canonical representative of an M31 element.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NonCanonicalM31Word {
    value: u32,
}

impl NonCanonicalM31Word {
    /// Returns the rejected raw word.
    pub const fn value(self) -> u32 {
        self.value
    }
}

impl fmt::Display for NonCanonicalM31Word {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "0x{:08x} is not a canonical M31 word",
            self.value
        )
    }
}

impl std::error::Error for NonCanonicalM31Word {}

/// An eight-word digest with canonical M31 limbs.
#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq)]
#[repr(transparent)]
pub struct Digest8([M31Word; 8]);

impl Digest8 {
    /// The all-zero digest.
    pub const ZERO: Self = Self([M31Word::ZERO; 8]);

    /// Constructs a digest from already checked words.
    pub const fn new(words: [M31Word; 8]) -> Self {
        Self(words)
    }

    /// Borrows the digest words in transcript order.
    pub const fn words(&self) -> &[M31Word; 8] {
        &self.0
    }

    /// Returns the digest words in transcript order.
    pub const fn into_words(self) -> [M31Word; 8] {
        self.0
    }
}

impl TryFrom<[u32; 8]> for Digest8 {
    type Error = NonCanonicalM31Word;

    fn try_from(words: [u32; 8]) -> Result<Self, Self::Error> {
        let [w0, w1, w2, w3, w4, w5, w6, w7] = words;
        Ok(Self::new([
            M31Word::try_from(w0)?,
            M31Word::try_from(w1)?,
            M31Word::try_from(w2)?,
            M31Word::try_from(w3)?,
            M31Word::try_from(w4)?,
            M31Word::try_from(w5)?,
            M31Word::try_from(w6)?,
            M31Word::try_from(w7)?,
        ]))
    }
}

macro_rules! semantic_digest {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq)]
        #[repr(transparent)]
        pub struct $name(Digest8);

        impl $name {
            /// Borrows the underlying full-width digest.
            pub const fn digest(&self) -> &Digest8 {
                &self.0
            }

            /// Returns the underlying full-width digest.
            pub const fn into_digest(self) -> Digest8 {
                self.0
            }
        }

        impl From<Digest8> for $name {
            fn from(value: Digest8) -> Self {
                Self(value)
            }
        }
    };
}

semantic_digest!(
    ProgramDigest,
    "Commitment to the canonical program image used by the VM AIR."
);
semantic_digest!(
    MemoryDigest,
    "Commitment to a canonical read-write memory state."
);
semantic_digest!(
    IoDigest,
    "Commitment to one canonical public IO stream or state."
);
semantic_digest!(
    ProtocolId,
    "Identity of one complete versioned proof protocol."
);
semantic_digest!(
    HashSuiteDigest,
    "Commitment to the hash construction and its domain assignments."
);
semantic_digest!(
    VmPreprocessingDigest,
    "Commitment to the VM verifier's trusted preprocessing."
);
semantic_digest!(
    RecursionPreprocessingDigest,
    "Commitment to the recursion verifier's trusted preprocessing."
);
semantic_digest!(
    VmAirProgramDigest,
    "Commitment to the fixed VM AIR evaluation program."
);
semantic_digest!(
    Poseidon2AirProgramDigest,
    "Commitment to the detached Poseidon2 AIR evaluation program."
);
semantic_digest!(
    RecursionAirProgramDigest,
    "Commitment to the fixed recursion AIR evaluation program."
);
semantic_digest!(
    VmPublicClaimDigest,
    "Commitment to the complete VM public claim hidden inside a recursion leaf."
);

#[cfg(test)]
mod tests {
    use core::any::TypeId;

    use rstest::rstest;

    use super::*;

    #[rstest]
    #[case::modulus(P)]
    #[case::largest_u32(u32::MAX)]
    fn m31_word_rejects_non_canonical_values(#[case] value: u32) {
        assert_eq!(M31Word::try_from(value), Err(NonCanonicalM31Word { value }));
    }

    #[test]
    fn m31_word_accepts_largest_canonical_value() {
        assert_eq!(M31Word::try_from(P - 1).map(M31Word::as_u32), Ok(P - 1));
    }

    #[test]
    fn digest_rejects_a_non_canonical_limb() {
        assert_eq!(
            Digest8::try_from([0, 1, 2, 3, P, 5, 6, 7]),
            Err(NonCanonicalM31Word { value: P })
        );
    }

    #[test]
    fn vm_and_recursion_preprocessing_have_distinct_types() {
        assert_ne!(
            TypeId::of::<VmPreprocessingDigest>(),
            TypeId::of::<RecursionPreprocessingDigest>()
        );
    }

    #[test]
    fn program_and_memory_commitments_have_distinct_types() {
        assert_ne!(TypeId::of::<ProgramDigest>(), TypeId::of::<MemoryDigest>());
    }

    #[test]
    fn protocol_and_io_commitments_have_distinct_types() {
        assert_ne!(TypeId::of::<ProtocolId>(), TypeId::of::<IoDigest>());
    }

    #[test]
    fn vm_public_claim_and_protocol_commitments_have_distinct_types() {
        assert_ne!(
            TypeId::of::<VmPublicClaimDigest>(),
            TypeId::of::<ProtocolId>()
        );
    }
}
