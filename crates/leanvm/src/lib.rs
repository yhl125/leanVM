//! leanVM proves leanXMSS and leanSPHINCS signature claims and LeanDA blob well-formedness.
//!
//! Release only: the zkDSL compiler [`setup`] runs overflows the debug stack.
//!
//! End to end in [`crates/leanvm/tests/api.rs`](https://github.com/leanEthereum/leanVM/blob/main/crates/leanvm/tests/api.rs).

pub use rec_aggregation::{
    AggregateVerifyError, AggregationError, EthereumClaims, EthereumProof, LeanSphincsClaim, LeanXmssClaim, MAX_KEYS,
    MAX_RECURSIONS, SnarkProveError, SnarkVerifyError, aggregate,
};

pub use leanvm_core::pcs::{MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};

/// LeanDA commitments. Blob symbols are `u64` words read in little-endian byte order.
pub mod lean_da {
    pub use ::lean_da::{
        BLOB_SYMBOLS, BlobSizeError, CELL_SYMBOLS, CELLS_PER_ROW, CODEWORD_SYMBOLS, DA_LOG_CELL, DA_LOG_K, DA_MAX_ROWS,
        DaWitness, commit,
    };
}

pub mod lean_xmss {
    pub use signatures::lean_xmss::{
        Digest, LOG_LIFETIME, LeafIndex, LeanXmssPublicKey, LeanXmssSecretKey, LeanXmssSignError, LeanXmssSignature,
        LeanXmssVerifyError, MESSAGE_LEN, Message, PUB_KEY_SIZE, PublicParam, SEED_LEN, SIG_SIZE, Seed, key_gen,
        key_gen_from_seed, sign, verify,
    };
}

pub mod lean_sphincs {
    pub use signatures::lean_sphincs::{
        Digest, LeanSphincsPublicKey, LeanSphincsSecretKey, LeanSphincsSignError, LeanSphincsSignature,
        LeanSphincsVerifyError, MESSAGE_LEN, Message, PUB_KEY_SIZE, PkSeed, SEED_LEN, SIG_SIZE, Seed, key_gen,
        key_gen_from_seed, sign, verify,
    };
}

/// Call once before [`aggregate`] or [`EthereumProof::verify`].
///
/// A proof's buffers are ordinary heap allocations, freed before it returns, so
/// proving speed depends on the process's global allocator. One that keeps freed
/// pages mapped serves the next proof from them with no page fault: jemalloc with
/// dirty pages that never decay, which the `leanvm` CLI installs. glibc's default
/// is the slow case, since it unmaps a large block on free.
pub fn setup() {
    leanvm_core::init_prover();
    rec_aggregation::warm_up();
}

/// Pure FIPS 205 SLH-DSA-SHAKE-128s, with message and context supplied by the verifier.
pub mod slh_dsa_shake_128s {
    pub use rec_aggregation::slh_dsa_shake_128s::{Claim, Error, Proof, Signature, batch, prove, warm_up};
    pub use signatures::slh_dsa_shake_128s::{
        Error as SignatureError, MAX_MESSAGE_BYTES, PUBLIC_KEY_BYTES, SIGNATURE_BYTES, verify as verify_signature,
    };
}
