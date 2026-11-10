//! A full PQTS leanSPHINCS verification in leanVM's existing VM, Keccak GKR and PCS.
//! The public statement is the expected key and message, not a designated raw signature.
//! Hints are internal checked witness data. This path is not zero knowledge and is not
//! covered by the formal proof of the different upstream `lean_sphincs` profile.

pub mod batch;

use std::collections::BTreeMap;
use std::sync::OnceLock;

use lean_compiler::{compile, parse_with_replacements};
use leanvm_core::cpu::{self, Program, Stats};
use primitives::{
    field::{F192, g_pow},
    hash,
};
use signatures::pqts_lean_sphincs::{self, HEIGHTS, LAYER_STARTS};
pub use signatures::pqts_lean_sphincs::{Claim, Signature};

const DOMAIN: &[u8; 16] = b"leanvm-pr152-v1\0";
const PROOF_MAGIC: &[u8; 8] = b"LVPQTP01";
const MAX_PROOF_BYTES: usize = 64 * 1024 * 1024;

#[derive(Debug)]
pub enum Error {
    Batch(&'static str),
    Recursion(crate::aggregation::AggregationError),
    Guest(cpu::ExecError),
    UnconstrainedReads,
    Prove(cpu::ProveError),
    Verify(cpu::CpuError),
    Codec(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Batch(error) => write!(f, "batch: {error}"),
            Self::Recursion(error) => write!(f, "recursion: {error}"),
            Self::Guest(error) => write!(f, "guest: {error}"),
            Self::UnconstrainedReads => write!(f, "guest: unconstrained reads"),
            Self::Prove(error) => write!(f, "prove: {error}"),
            Self::Verify(error) => write!(f, "verify: {error:?}"),
            Self::Codec(error) => write!(f, "codec: {error}"),
        }
    }
}
impl std::error::Error for Error {}

fn cell(bytes: &[u8]) -> F192 {
    assert_eq!(bytes.len(), 16);
    F192::new(
        u64::from_le_bytes(bytes[..8].try_into().unwrap()),
        u64::from_le_bytes(bytes[8..].try_into().unwrap()),
        0,
    )
}

fn public_input(claim: &Claim) -> [F192; 2] {
    let digest = hash::Hasher::new()
        .update(DOMAIN)
        .update(&claim.public_key)
        .update(&claim.message)
        .finalize();
    [cell(&digest[..16]), cell(&digest[16..])]
}

fn program() -> &'static Program {
    static PROGRAM: OnceLock<Program> = OnceLock::new();
    PROGRAM.get_or_init(|| {
        let _span = tracing::info_span!("PQTS leanSPHINCS compile").entered();
        let replacements = BTreeMap::from([(
            "DOMAIN_PLACEHOLDER".to_string(),
            u128::from_le_bytes(*DOMAIN).to_string(),
        )]);
        compile(
            &parse_with_replacements(include_str!("../guests/pqts_lean_sphincs.py"), &replacements)
                .expect("PQTS leanSPHINCS guest parses"),
        )
    })
}

type Hints = BTreeMap<&'static str, Vec<Vec<F192>>>;

fn bit_cells(bytes: &[u8]) -> Vec<F192> {
    (0..8 * bytes.len())
        .map(|i| F192::new(u64::from((bytes[i / 8] >> (i % 8)) & 1), 0, 0))
        .collect()
}

fn advice(claim: &Claim, signature: &Signature) -> Hints {
    let _span = tracing::info_span!("PQTS leanSPHINCS advice").entered();
    // Recovery deliberately has no accept gate. The guest must reject invalid advice.
    let recovered = pqts_lean_sphincs::recover(claim, signature);
    let mut hints = Hints::new();
    hints.insert(
        "claim",
        vec![vec![
            cell(&claim.public_key[..16]),
            cell(&claim.public_key[16..]),
            cell(&claim.message[..16]),
            cell(&claim.message[16..]),
        ]],
    );
    hints.insert("randomizer", vec![vec![cell(&signature.digest(0))]]);
    hints.insert("digest_bits", vec![bit_cells(&recovered.digest)]);
    hints.insert(
        "fors_secret",
        (0..24)
            .map(|tree| vec![cell(&signature.digest(16 + 176 * tree))])
            .collect(),
    );
    hints.insert(
        "fors_sibling",
        (0..24)
            .flat_map(|tree| (0..10).map(move |level| vec![cell(&signature.digest(32 + 176 * tree + 16 * level))]))
            .collect(),
    );
    hints.insert(
        "counter",
        (0..3)
            .map(|layer| bit_cells(&signature.counter(layer).to_le_bytes()))
            .collect(),
    );
    hints.insert(
        "wots",
        (0..3)
            .flat_map(|layer| {
                (0..64).map(move |chain| vec![cell(&signature.digest(LAYER_STARTS[layer] + 4 + 16 * chain))])
            })
            .collect(),
    );
    hints.insert(
        "digit",
        recovered
            .encodings
            .iter()
            .flat_map(|encoding| {
                pqts_lean_sphincs::digits(encoding)
                    .into_iter()
                    .map(|digit| vec![F192::from(g_pow(usize::from(digit)))])
            })
            .collect(),
    );
    hints.insert(
        "ht_sibling",
        (0..3)
            .flat_map(|layer| {
                (0..HEIGHTS[layer])
                    .map(move |level| vec![cell(&signature.digest(LAYER_STARTS[layer] + 1028 + 16 * level))])
            })
            .collect(),
    );
    hints
}

fn with_advice(hints: Hints) -> Program {
    let mut guest = program().clone();
    for (name, entries) in hints {
        guest.set_witness(name, entries);
    }
    guest
}

/// Execute every guest constraint without making a proof. Invalid signatures are not prefiltered.
#[cfg(test)]
#[tracing::instrument(name = "PQTS leanSPHINCS guest check", skip_all)]
fn check_guest(claim: &Claim, signature: &Signature) -> Result<cpu::Execution, Error> {
    let execution = with_advice(advice(claim, signature))
        .execute(public_input(claim))
        .map_err(Error::Guest)?;
    if !execution.unconstrained_reads.is_empty() {
        return Err(Error::UnconstrainedReads);
    }
    Ok(execution)
}

/// Prove the complete relation, with no native-reference acceptance shortcut.
#[tracing::instrument(name = "PQTS leanSPHINCS prove", skip_all)]
pub fn prove(claim: &Claim, signature: &Signature, log_inv_rate: usize) -> Result<(Proof, Stats), Error> {
    tracing::info_span!("PQTS leanSPHINCS pool setup").in_scope(leanvm_core::init_prover);
    let guest = with_advice(advice(claim, signature));
    let (proof, stats) = cpu::prove(&guest, public_input(claim), log_inv_rate).map_err(Error::Prove)?;
    Ok((Proof(proof), stats))
}

/// Only the existing leanVM proof transport plus a PQTS leanSPHINCS version and exact byte length.
pub struct Proof(cpu::Proof);

impl Proof {
    pub fn to_bytes(&self) -> Result<Vec<u8>, Error> {
        let body = self.0.to_bytes();
        if body.len() > MAX_PROOF_BYTES {
            return Err(Error::Codec("proof exceeds size limit".into()));
        }
        let mut out = Vec::with_capacity(16 + body.len());
        out.extend_from_slice(PROOF_MAGIC);
        out.extend_from_slice(&(body.len() as u64).to_le_bytes());
        out.extend_from_slice(&body);
        Ok(out)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() < 16 || bytes.len() > MAX_PROOF_BYTES + 16 || &bytes[..8] != PROOF_MAGIC {
            return Err(Error::Codec("version/length".into()));
        }
        let declared = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
        if declared != (bytes.len() - 16) as u64 {
            return Err(Error::Codec("body length/trailing bytes".into()));
        }
        cpu::Proof::from_bytes(&bytes[16..])
            .map(Self)
            .ok_or_else(|| Error::Codec("invalid proof encoding".into()))
    }

    /// The independently expected key/message and proof suffice. No signature or advice is read.
    #[tracing::instrument(name = "PQTS leanSPHINCS verify", skip_all)]
    pub fn verify(&self, expected: &Claim) -> Result<(), Error> {
        cpu::verify(program(), &public_input(expected), &self.0)
            .map(|_| ())
            .map_err(Error::Verify)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kat() -> (Claim, Signature) {
        (
            Claim::from_bytes(
                include_bytes!("../../signatures/tests/pqts_lean_sphincs/kat-pk.bin"),
                include_bytes!("../../signatures/tests/pqts_lean_sphincs/kat-message.bin"),
            )
            .unwrap(),
            Signature::from_bytes(include_bytes!(
                "../../signatures/tests/pqts_lean_sphincs/kat-signature.bin"
            ))
            .unwrap(),
        )
    }

    fn rejected(claim: &Claim, hints: Hints, name: &str) {
        assert!(
            with_advice(hints).execute(public_input(claim)).is_err(),
            "{name}: invalid witness accepted"
        );
    }

    #[test]
    fn guest_checks_raw_and_hints() {
        let (claim, signature) = kat();
        let execution = check_guest(&claim, &signature).unwrap();
        assert_eq!(execution.rows()[5], 493); // PQTS leanSPHINCS plus the public statement hash.
        assert!(execution.unconstrained_reads.is_empty());
        drop(execution);
        let good = advice(&claim, &signature);
        let mut other = claim.clone();
        other.message[0] ^= 1;
        rejected(&other, good.clone(), "expected-message");
        rejected(&other, advice(&other, &signature), "bad-message-regenerated-advice");
        let mut raw = *signature.as_bytes();
        raw[7739] ^= 1;
        rejected(
            &claim,
            advice(&claim, &Signature::from_bytes(&raw).unwrap()),
            "bad-signature-last-root-edge",
        );
        let mut hints = good.clone();
        hints.get_mut("digest_bits").unwrap()[0][256] += F192::ONE;
        rejected(&claim, hints, "second-Hmsg-crossing-FORS-bit");
        let mut hints = good.clone();
        hints.get_mut("digest_bits").unwrap()[0][0] = F192::new(2, 0, 0);
        rejected(&claim, hints, "non-boolean-digest-bit");
        let mut hints = good.clone();
        hints.get_mut("counter").unwrap()[0][31] = F192::new(2, 0, 0);
        rejected(&claim, hints, "non-boolean-counter-bit");
        let mut hints = good.clone();
        hints.get_mut("digit").unwrap()[0][0] = F192::from(g_pow(4));
        rejected(&claim, hints, "out-of-range-digit");
        let mut hints = good.clone();
        hints.get_mut("randomizer").unwrap()[0][0] += F192::ONE;
        rejected(&claim, hints, "shared-randomizer");
        let zero_step = good["digit"]
            .iter()
            .position(|digit| digit[0] == F192::from(g_pow(3)))
            .unwrap();
        let mut hints = good.clone();
        hints.get_mut("wots").unwrap()[zero_step][0] += F192::ONE;
        rejected(&claim, hints, "zero-step-endpoint");
        let mut hints = good;
        hints.get_mut("claim").unwrap()[0][0].c2 = 1;
        rejected(&claim, hints, "noncanonical-public-cell");
    }
}
