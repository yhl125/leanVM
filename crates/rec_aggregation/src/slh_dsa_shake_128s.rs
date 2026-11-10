//! FIPS 205 SHAKE-128s guest; expected key, message and context are public.
//! Existing VM/GKR/PCS and proof transport, with a separate program and wire version.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use lean_compiler::{compile, parse_with_replacements};
use leanvm_core::cpu::{self, Program, Stats};
use primitives::{
    field::{F192, g_pow},
    hash,
};
use signatures::slh_dsa_shake_128s;
pub use signatures::slh_dsa_shake_128s::{Claim, Signature};
#[derive(Debug)]
pub enum Error {
    Batch(&'static str),
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
            Self::Guest(error) => write!(f, "guest: {error}"),
            Self::UnconstrainedReads => write!(f, "guest: unconstrained reads"),
            Self::Prove(error) => write!(f, "prove: {error}"),
            Self::Verify(error) => write!(f, "verify: {error:?}"),
            Self::Codec(error) => write!(f, "codec: {error}"),
        }
    }
}
impl std::error::Error for Error {}

pub mod batch;

const DOMAIN: &[u8; 16] = b"SLH-SHAKE128s-v1";
const PROOF_MAGIC: &[u8; 8] = b"LVSHKP01";
const MAX_PROOF_BYTES: usize = 64 * 1024 * 1024;
type Hints = BTreeMap<&'static str, Vec<Vec<F192>>>;

fn cell(bytes: &[u8]) -> F192 {
    let mut padded = [0; 16];
    padded[..bytes.len()].copy_from_slice(bytes);
    F192::new(
        u64::from_le_bytes(padded[..8].try_into().unwrap()),
        u64::from_le_bytes(padded[8..].try_into().unwrap()),
        0,
    )
}
fn lengths(claim: &Claim) -> [u8; 16] {
    let mut bytes = [0; 16];
    bytes[..8].copy_from_slice(&(claim.context.len() as u64).to_le_bytes());
    bytes[8..].copy_from_slice(&(claim.message.len() as u64).to_le_bytes());
    bytes
}
fn public_input(claim: &Claim) -> [F192; 2] {
    let digest = hash::Hasher::new()
        .update(DOMAIN)
        .update(&lengths(claim))
        .update(&claim.public_key)
        .update(&claim.external_message())
        .finalize();
    [cell(&digest[..16]), cell(&digest[16..])]
}
struct Context {
    shape: (usize, usize),
    program: Program,
    bytecode: verifier::Bytecode,
}
fn context(claim: &Claim) -> Arc<Context> {
    static PROGRAM: Mutex<Option<Arc<Context>>> = Mutex::new(None);
    let shape = (claim.message.len(), claim.context.len());
    let mut cached = PROGRAM.lock().unwrap();
    if let Some(context) = cached.as_ref().filter(|context| context.shape == shape) {
        return context.clone();
    }
    let _span = tracing::info_span!("SLH compile").entered();
    let replacements = BTreeMap::from([
        ("DOMAIN_PLACEHOLDER".into(), u128::from_le_bytes(*DOMAIN).to_string()),
        (
            "LENGTHS_PLACEHOLDER".into(),
            u128::from_le_bytes(lengths(claim)).to_string(),
        ),
        (
            "MPLEN_PLACEHOLDER".into(),
            (2 + claim.context.len() + claim.message.len()).to_string(),
        ),
        ("CTXLEN_PLACEHOLDER".into(), claim.context.len().to_string()),
    ]);
    let program = compile(
        &parse_with_replacements(include_str!("../guests/slh_dsa_shake_128s.py"), &replacements)
            .expect("SLH guest parses"),
    );
    let table = cpu::layout::bytecode_table(&program.prog)
        .iter()
        .map(|word| word.0)
        .collect::<Vec<_>>();
    let context = Arc::new(Context {
        shape,
        program,
        bytecode: verifier::Bytecode::new(&table),
    });
    *cached = Some(context.clone());
    context
}
fn bit_cells(bytes: &[u8]) -> Vec<F192> {
    (0..8 * bytes.len())
        .map(|i| F192::new(u64::from((bytes[i / 8] >> (i % 8)) & 1), 0, 0))
        .collect()
}
fn advice(claim: &Claim, signature: &Signature) -> Hints {
    let _span = tracing::info_span!("SLH advice").entered();
    let recovered = slh_dsa_shake_128s::recover(claim, signature);
    let mut hints = Hints::new();
    let mut claim_cells = claim.public_key.chunks(16).map(cell).collect::<Vec<_>>();
    claim_cells.extend(claim.external_message().chunks(16).map(cell));
    hints.insert("claim", vec![claim_cells]);
    hints.insert("randomizer", vec![vec![cell(&signature.node(0))]]);
    hints.insert("digest_bits", vec![bit_cells(&recovered.digest)]);
    hints.insert(
        "fors_secret",
        (0..14).map(|t| vec![cell(&signature.node(16 + 208 * t))]).collect(),
    );
    hints.insert(
        "fors_sibling",
        (0..14)
            .flat_map(|t| (0..12).map(move |j| vec![cell(&signature.node(32 + 208 * t + 16 * j))]))
            .collect(),
    );
    hints.insert(
        "wots",
        (0..7)
            .flat_map(|l| (0..35).map(move |j| vec![cell(&signature.node(2928 + 704 * l + 16 * j))]))
            .collect(),
    );
    hints.insert(
        "digit",
        recovered
            .signed
            .iter()
            .flat_map(|node| {
                slh_dsa_shake_128s::digits(node)
                    .into_iter()
                    .map(|d| vec![F192::from(g_pow(usize::from(d)))])
            })
            .collect(),
    );
    hints.insert(
        "ht_sibling",
        (0..7)
            .flat_map(|l| (0..9).map(move |j| vec![cell(&signature.node(3488 + 704 * l + 16 * j))]))
            .collect(),
    );
    hints
}
fn with_advice(claim: &Claim, hints: Hints) -> Program {
    let mut guest = context(claim).program.clone();
    for (name, entries) in hints {
        guest.set_witness(name, entries);
    }
    guest
}
fn valid(claim: &Claim) -> Result<(), Error> {
    claim.validate().map_err(|e| Error::Codec(e.to_string()))
}

#[cfg(test)]
#[tracing::instrument(name = "SLH guest check", skip_all)]
fn check_guest(claim: &Claim, signature: &Signature) -> Result<cpu::Execution, Error> {
    valid(claim)?;
    let execution = with_advice(claim, advice(claim, signature))
        .execute(public_input(claim))
        .map_err(Error::Guest)?;
    if !execution.unconstrained_reads.is_empty() {
        return Err(Error::UnconstrainedReads);
    }
    Ok(execution)
}

/// Compile the program and verifier tables for this message/context length.
pub fn warm_up(claim: &Claim) -> Result<(), Error> {
    valid(claim)?;
    let _ = context(claim);
    Ok(())
}

#[tracing::instrument(name = "SLH prove", skip_all)]
pub fn prove(claim: &Claim, signature: &Signature) -> Result<(Proof, Stats), Error> {
    valid(claim)?;
    tracing::info_span!("SLH pool setup").in_scope(leanvm_core::init_prover);
    let guest = with_advice(claim, advice(claim, signature));
    let (proof, stats) =
        cpu::prove(&guest, public_input(claim), leanvm_core::pcs::TEST_LOG_INV_RATE).map_err(Error::Prove)?;
    Ok((Proof(proof), stats))
}

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
        if u64::from_le_bytes(bytes[8..16].try_into().unwrap()) != (bytes.len() - 16) as u64 {
            return Err(Error::Codec("body length/trailing bytes".into()));
        }
        cpu::Proof::from_bytes(&bytes[16..])
            .map(Self)
            .ok_or_else(|| Error::Codec("invalid proof encoding".into()))
    }
    #[tracing::instrument(name = "SLH verify", skip_all)]
    pub fn verify(&self, expected: &Claim) -> Result<(), Error> {
        valid(expected)?;
        verifier::verify_execution(
            &context(expected).bytecode,
            &cpu::public_input_bytes(&public_input(expected)),
            &cpu::scalar_proof(&self.0),
        )
        .map(|_| ())
        .map_err(|e| Error::Verify(cpu::CpuError::Verifier(e)))
    }
}

#[cfg(test)]
fn kat() -> (Claim, Signature) {
    (
        Claim::from_bytes(
            include_bytes!("../../signatures/tests/slh_dsa_shake_128s/tc343.pk"),
            include_bytes!("../../signatures/tests/slh_dsa_shake_128s/tc343.message"),
            include_bytes!("../../signatures/tests/slh_dsa_shake_128s/tc343.context"),
        )
        .unwrap(),
        Signature::from_bytes(include_bytes!(
            "../../signatures/tests/slh_dsa_shake_128s/tc343.signature"
        ))
        .unwrap(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_answer_and_invalid_witnesses() {
        let (claim, signature) = kat();
        drop(check_guest(&claim, &signature).unwrap());
        let good = advice(&claim, &signature);
        let mut cases = Vec::new();
        for (name, offset) in [
            ("randomizer", 0),
            ("fors-secret", 16),
            ("fors-auth", 32),
            ("wots", 2928),
            ("last-xmss-auth", 7855),
        ] {
            let mut raw = *signature.as_bytes();
            raw[offset] ^= 1;
            cases.push((
                name,
                claim.clone(),
                advice(&claim, &Signature::from_bytes(&raw).unwrap()),
            ));
        }
        for name in ["expected-message", "expected-key", "expected-context"] {
            let mut other = claim.clone();
            match name {
                "expected-message" => {
                    if other.message.is_empty() {
                        other.message.push(1);
                    } else {
                        other.message[0] ^= 1;
                    }
                }
                "expected-key" => other.public_key[0] ^= 1,
                _ => {
                    if other.context.is_empty() {
                        other.context.push(1);
                    } else {
                        other.context[0] ^= 1;
                    }
                }
            }
            cases.push((name, other, good.clone()));
        }
        for (name, stream, entry, offset, value) in [
            ("nonboolean-hmsg", "digest_bits", 0, 0, F192::new(2, 0, 0)),
            (
                "wrong-hmsg-tree-bit",
                "digest_bits",
                0,
                168,
                good["digest_bits"][0][168] + F192::ONE,
            ),
            ("wots-digit-range", "digit", 0, 0, F192::from(g_pow(16))),
            ("wots-checksum", "digit", 32, 0, F192::from(g_pow(15))),
            (
                "noncanonical-claim",
                "claim",
                0,
                0,
                good["claim"][0][0] + F192::new(0, 0, 1),
            ),
        ] {
            let mut hints = good.clone();
            hints.get_mut(stream).unwrap()[entry][offset] = value;
            cases.push((name, claim.clone(), hints));
        }
        for (name, expected, hints) in cases {
            // Keep the original witness shape so a changed expected context exercises binding.
            assert!(
                with_advice(&claim, hints).execute(public_input(&expected)).is_err(),
                "{name}: invalid witness accepted"
            );
        }
    }
}
