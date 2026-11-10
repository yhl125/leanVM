//! One complete standard SHAKE-128s execution proof for an ordered batch.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use lean_compiler::{compile, parse_with_replacements};
use leanvm_core::cpu::{self, Program, Stats};
use primitives::{
    field::{F192, g_pow},
    hash,
};

use super::{Claim, Context, DOMAIN, Error, Hints, MAX_PROOF_BYTES, Signature, advice, lengths, valid};

pub const MAX_CLAIMS: usize = 128;
pub const MAX_PUBLIC_BYTES: usize = 16 + MAX_CLAIMS * (48 + 255 + signatures::slh_dsa_shake_128s::MAX_MESSAGE_BYTES);
const PUBLIC_MAGIC: &[u8; 8] = b"LVMSLHC2";
const PROOF_MAGIC: &[u8; 8] = b"LVSHKB01";
const BATCH_DOMAIN: &[u8; 16] = b"SLH-BATCH-v2\0\0\0\0";

fn check_count(n: usize) -> Result<(), Error> {
    if !(1..=MAX_CLAIMS).contains(&n) {
        return Err(Error::Batch("SLH batch count must be in 1..=128"));
    }
    Ok(())
}

fn shape(claims: &[Claim]) -> Result<(usize, usize), Error> {
    check_count(claims.len())?;
    let shape = (claims[0].message.len(), claims[0].context.len());
    for claim in claims {
        valid(claim)?;
        if (claim.message.len(), claim.context.len()) != shape {
            return Err(Error::Batch("SLH batch requires one message/context length shape"));
        }
    }
    Ok(shape)
}

fn source() -> String {
    let (helpers, body) = include_str!("../../guests/slh_dsa_shake_128s.py")
        .split_once("\ndef main():")
        .expect("SLH main boundary");
    let public = "    public = GEN ** 0\n    public[1] = public_digest[0]\n    public[GEN] = public_digest[1]\n";
    assert_eq!(body.matches(public).count(), 1);
    let body = body.replacen(public, "", 1);
    let body = body.strip_suffix("    return\n").expect("SLH final return");
    format!(
        "{helpers}\n\ndef verify_slh():{body}    return public_digest[0], public_digest[1]\n\n{}",
        include_str!("../../guests/slh_dsa_shake_128s_batch.py")
    )
}

fn context(claims: &[Claim]) -> Result<Arc<Context>, Error> {
    static PROGRAM: Mutex<Option<Arc<Context>>> = Mutex::new(None);
    let shape = shape(claims)?;
    let mut cached = PROGRAM.lock().unwrap();
    if let Some(context) = cached.as_ref().filter(|context| context.shape == shape) {
        return Ok(context.clone());
    }
    let _span = tracing::info_span!("SLH batch compile").entered();
    let replacements = BTreeMap::from([
        ("DOMAIN_PLACEHOLDER".into(), u128::from_le_bytes(*DOMAIN).to_string()),
        (
            "LENGTHS_PLACEHOLDER".into(),
            u128::from_le_bytes(lengths(&claims[0])).to_string(),
        ),
        ("MPLEN_PLACEHOLDER".into(), (2 + shape.0 + shape.1).to_string()),
        ("CTXLEN_PLACEHOLDER".into(), shape.1.to_string()),
        ("BATCH_MAX_CLAIMS_PLACEHOLDER".into(), MAX_CLAIMS.to_string()),
        (
            "BATCH_DOMAIN_PLACEHOLDER".into(),
            u128::from_le_bytes(*BATCH_DOMAIN).to_string(),
        ),
    ]);
    let program = compile(&parse_with_replacements(&source(), &replacements).expect("SLH batch guest parses"));
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
    Ok(context)
}

fn public_input(claims: &[Claim]) -> [F192; 2] {
    let count = F192::from(g_pow(claims.len()));
    let mut state = hash::Hasher::new();
    state
        .update(BATCH_DOMAIN)
        .update(&count.c0.to_le_bytes())
        .update(&count.c1.to_le_bytes());
    for claim in claims {
        for cell in super::public_input(claim) {
            state.update(&cell.c0.to_le_bytes()).update(&cell.c1.to_le_bytes());
        }
    }
    for _ in claims.len()..MAX_CLAIMS {
        state.update(&[0; 32]);
    }
    let digest = state.finalize();
    [super::cell(&digest[..16]), super::cell(&digest[16..])]
}

pub fn public_to_bytes(claims: &[Claim]) -> Result<Vec<u8>, Error> {
    shape(claims)?;
    let mut out = Vec::new();
    out.extend_from_slice(PUBLIC_MAGIC);
    out.extend_from_slice(&(claims.len() as u64).to_le_bytes());
    for claim in claims {
        out.extend_from_slice(&claim.public_key);
        out.extend_from_slice(&lengths(claim));
        out.extend_from_slice(&claim.context);
        out.extend_from_slice(&claim.message);
    }
    Ok(out)
}

pub fn public_from_bytes(bytes: &[u8]) -> Result<Vec<Claim>, Error> {
    if bytes.len() < 16 || bytes.len() > MAX_PUBLIC_BYTES || &bytes[..8] != PUBLIC_MAGIC {
        return Err(Error::Batch("SLH public framing"));
    }
    let n = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
    if !(1..=MAX_CLAIMS as u64).contains(&n) {
        return Err(Error::Batch("SLH public count"));
    }
    let mut claims = Vec::with_capacity(n as usize);
    let mut cursor = 16;
    for _ in 0..n {
        let header = bytes
            .get(cursor..cursor + 48)
            .ok_or(Error::Batch("SLH public item header"))?;
        let context_len = u64::from_le_bytes(header[32..40].try_into().unwrap());
        let message_len = u64::from_le_bytes(header[40..48].try_into().unwrap());
        if context_len > 255 || message_len > signatures::slh_dsa_shake_128s::MAX_MESSAGE_BYTES as u64 {
            return Err(Error::Batch("SLH public item lengths"));
        }
        cursor += 48;
        let end = cursor + context_len as usize + message_len as usize;
        let data = bytes.get(cursor..end).ok_or(Error::Batch("SLH public item data"))?;
        claims.push(
            Claim::from_bytes(
                &header[..32],
                &data[context_len as usize..],
                &data[..context_len as usize],
            )
            .map_err(|e| Error::Codec(e.to_string()))?,
        );
        cursor = end;
    }
    if cursor != bytes.len() {
        return Err(Error::Batch("SLH public trailing bytes"));
    }
    shape(&claims)?;
    Ok(claims)
}

fn hints(claims: &[Claim], signatures: &[Signature]) -> Result<Hints, Error> {
    shape(claims)?;
    if signatures.len() != claims.len() {
        return Err(Error::Batch("one raw SLH signature per ordered claim"));
    }
    let mut hints = Hints::from([("batch_count", vec![vec![F192::from(g_pow(claims.len()))]])]);
    let items = parallel::map_collect(claims.len(), |i| advice(&claims[i], &signatures[i]));
    for item in items {
        for (name, entries) in item {
            hints.entry(name).or_default().extend(entries);
        }
    }
    Ok(hints)
}

fn with_hints(claims: &[Claim], hints: Hints) -> Result<Program, Error> {
    let mut program = context(claims)?.program.clone();
    for (name, entries) in hints {
        program.set_witness(name, entries);
    }
    Ok(program)
}

pub fn warm_up(claims: &[Claim]) -> Result<(), Error> {
    context(claims)?;
    Ok(())
}

#[cfg(test)]
#[tracing::instrument(name = "SLH batch guest check", skip_all)]
fn check_guest(claims: &[Claim], signatures: &[Signature]) -> Result<cpu::Execution, Error> {
    let execution = with_hints(claims, hints(claims, signatures)?)?
        .execute(public_input(claims))
        .map_err(Error::Guest)?;
    if !execution.unconstrained_reads.is_empty() {
        return Err(Error::UnconstrainedReads);
    }
    Ok(execution)
}

#[tracing::instrument(name = "SLH batch prove", skip_all)]
pub fn prove(claims: &[Claim], signatures: &[Signature]) -> Result<(Proof, Stats), Error> {
    shape(claims)?;
    tracing::info_span!("SLH batch pool setup").in_scope(leanvm_core::init_prover);
    let guest = with_hints(claims, hints(claims, signatures)?)?;
    let (inner, stats) =
        cpu::prove(&guest, public_input(claims), leanvm_core::pcs::TEST_LOG_INV_RATE).map_err(Error::Prove)?;
    Ok((
        Proof {
            count: claims.len(),
            inner,
        },
        stats,
    ))
}

pub struct Proof {
    count: usize,
    inner: cpu::Proof,
}
impl Proof {
    pub fn to_bytes(&self) -> Result<Vec<u8>, Error> {
        let body = self.inner.to_bytes();
        if body.len() > MAX_PROOF_BYTES {
            return Err(Error::Codec("proof exceeds size limit".into()));
        }
        let mut out = Vec::with_capacity(24 + body.len());
        out.extend_from_slice(PROOF_MAGIC);
        out.extend_from_slice(&(self.count as u64).to_le_bytes());
        out.extend_from_slice(&(body.len() as u64).to_le_bytes());
        out.extend_from_slice(&body);
        Ok(out)
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() < 24 || bytes.len() > MAX_PROOF_BYTES + 24 || &bytes[..8] != PROOF_MAGIC {
            return Err(Error::Batch("SLH batch proof framing"));
        }
        let n = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
        if !(1..=MAX_CLAIMS as u64).contains(&n)
            || u64::from_le_bytes(bytes[16..24].try_into().unwrap()) != (bytes.len() - 24) as u64
        {
            return Err(Error::Batch("SLH batch proof count/length"));
        }
        cpu::Proof::from_bytes(&bytes[24..])
            .map(|inner| Self {
                count: n as usize,
                inner,
            })
            .ok_or_else(|| Error::Codec("invalid proof encoding".into()))
    }
    #[tracing::instrument(name = "SLH batch verify", skip_all)]
    pub fn verify(&self, expected: &[Claim]) -> Result<(), Error> {
        shape(expected)?;
        if self.count != expected.len() {
            return Err(Error::Batch("SLH batch expected count"));
        }
        verifier::verify_execution(
            &context(expected)?.bytecode,
            &cpu::public_input_bytes(&public_input(expected)),
            &cpu::scalar_proof(&self.inner),
        )
        .map(|_| ())
        .map_err(|e| Error::Verify(cpu::CpuError::Verifier(e)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn batch_binds_last_signature_and_count() {
        let (claim, signature) = super::super::kat();
        let claims = [claim.clone(), claim];
        let signatures = [signature.clone(), signature];
        drop(check_guest(&claims, &signatures).unwrap());
        let good = hints(&claims, &signatures).unwrap();
        let mut changed = claims.clone();
        changed[1].message[0] ^= 1;
        assert!(
            with_hints(&claims, good.clone())
                .unwrap()
                .execute(public_input(&changed))
                .is_err()
        );
        let mut raw = *signatures[1].as_bytes();
        *raw.last_mut().unwrap() ^= 1;
        let broken = [signatures[0].clone(), Signature::from_bytes(&raw).unwrap()];
        assert!(check_guest(&claims, &broken).is_err());
        for stream in ["batch_count", "claim"] {
            let mut bad = good.clone();
            if stream == "batch_count" {
                bad.get_mut(stream).unwrap()[0][0] = F192::from(g_pow(1));
            } else {
                bad.get_mut(stream).unwrap()[1][0] += F192::new(0, 0, 1);
            }
            assert!(
                with_hints(&claims, bad)
                    .unwrap()
                    .execute(public_input(&claims))
                    .is_err(),
                "{stream}"
            );
        }
    }

    #[test]
    fn public_codec_count_order_shape() {
        let a = Claim::from_bytes(&[1; 32], &[2; 32], &[]).unwrap();
        let b = Claim::from_bytes(&[3; 32], &[4; 32], &[]).unwrap();
        let claims = [a, b];
        let bytes = public_to_bytes(&claims).unwrap();
        assert_eq!(bytes.len(), 176);
        assert_eq!(public_from_bytes(&bytes).unwrap(), claims);
        assert_ne!(
            public_input(&claims),
            public_input(&[claims[1].clone(), claims[0].clone()])
        );
        for cut in [0, 15, 16, 63, 175] {
            assert!(public_from_bytes(&bytes[..cut]).is_err());
        }
        assert!(public_from_bytes(&[bytes.as_slice(), &[0]].concat()).is_err());
        for n in [0u64, 1, 3, 129, u64::MAX] {
            let mut malformed = bytes.clone();
            malformed[8..16].copy_from_slice(&n.to_le_bytes());
            assert!(public_from_bytes(&malformed).is_err());
        }
        let mut other = claims.clone();
        other[1].context.push(1);
        assert!(public_to_bytes(&other).is_err());
        assert!(public_to_bytes(&[]).is_err());
        assert!(public_to_bytes(&vec![claims[0].clone(); 129]).is_err());
        assert_eq!(
            public_from_bytes(&public_to_bytes(&vec![claims[0].clone(); 128]).unwrap())
                .unwrap()
                .len(),
            128
        );
        assert_eq!(source().matches("def main():").count(), 1);
        assert_eq!(source().matches("def verify_slh():").count(), 1);
    }
}
