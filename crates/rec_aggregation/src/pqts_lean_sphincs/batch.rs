//! Ordered PQTS leanSPHINCS batches, using one guest for raw leaves and recursive nodes.
//! Repeated statements retain their positions and every raw signature is checked.

use std::sync::OnceLock;

use lean_compiler::{compile, parse_with_replacements};
use leanvm_core::cpu::{self, Program, Stats, from_scalar, public_input_bytes, scalar_proof, to_scalar};
use primitives::{
    field::{F64, F192, g_pow},
    hash,
};

use super::{Claim, Error, Hints, MAX_PROOF_BYTES, Signature, advice, cell};
use crate::aggregation::{self, DeferredClaim, list_split};

pub const MAX_CLAIMS: usize = 512;
pub const LOG_INV_RATE: usize = leanvm_core::pcs::TEST_LOG_INV_RATE;
const PUBLIC_MAGIC: &[u8; 8] = b"LVM152C2";
const PROOF_MAGIC: &[u8; 8] = b"LVPQTB01";

fn count(n: usize) -> F192 {
    F192::from(g_pow(n))
}

fn check_count(n: usize) -> Result<(), Error> {
    if !(1..=MAX_CLAIMS).contains(&n) {
        return Err(Error::Batch("claim count must be in 1..=512"));
    }
    Ok(())
}

fn source() -> String {
    let (helpers, old_main) = include_str!("../../guests/lean_ethereum.py")
        .split_once("\ndef main():")
        .expect("upstream main boundary");
    let (_, batching) = old_main
        .split_once("\ndef aggregate_claims(")
        .expect("upstream batching helper");
    let (raw_helpers, raw_main) = include_str!("../../guests/pqts_lean_sphincs.py")
        .split_once("\ndef main():")
        .expect("PQTS leanSPHINCS main boundary");
    let (raw_globals, raw_helpers) = raw_helpers
        .split_once("\n@inline\n")
        .expect("PQTS leanSPHINCS declaration boundary");
    let (batch_globals, batch_main) = include_str!("../../guests/pqts_lean_sphincs_batch.py")
        .split_once("\ndef main():")
        .expect("PQTS leanSPHINCS batch declaration boundary");
    let (_, raw_body) = raw_main
        .split_once("    pp = claim[1]\n")
        .expect("PQTS leanSPHINCS verification body");
    let source = format!(
        "{raw_globals}\n{batch_globals}\n{helpers}\ndef aggregate_claims({batching}\n@inline\n{raw_helpers}\n\ndef verify_pr152(claim: StackBuf(4)):\n    pp = claim[1]\n{raw_body}\n\ndef main():{batch_main}"
    );
    // The shared coverage helper additionally pins each child position to the next parent slot.
    let index = "    off_hint = hint_witness(\"child_claim_index\")\n";
    assert_eq!(source.matches(index).count(), 1);
    let source = source.replacen(
        index,
        &format!("{index}        assert off_hint == marks * (GEN ** j)\n"),
        1,
    );
    let rate = "    rate_sel = g_power_of_word(log_inv_rate) / GEN\n";
    assert_eq!(source.matches(rate).count(), 1);
    source.replacen(rate, &format!("    assert log_inv_rate == {LOG_INV_RATE}\n{rate}"), 1)
}

struct Context {
    program: Program,
    table: Vec<F64>,
    scalar: verifier::Bytecode,
    live_rows: std::ops::Range<usize>,
}

fn context() -> &'static Context {
    static CONTEXT: OnceLock<Context> = OnceLock::new();
    CONTEXT.get_or_init(|| {
        let _span = tracing::info_span!("PQTS leanSPHINCS batch compile").entered();
        let source = source();
        let mut guess = 20;
        for _ in 0..8 {
            let mut replacements = aggregation::placeholder_map(guess);
            replacements.insert(
                "DOMAIN_PLACEHOLDER".into(),
                u128::from_le_bytes(*super::DOMAIN).to_string(),
            );
            replacements.insert("PR152_MAX_CLAIMS_PLACEHOLDER".into(), MAX_CLAIMS.to_string());
            let mut program =
                compile(&parse_with_replacements(&source, &replacements).expect("PQTS leanSPHINCS batch guest parses"));
            let actual = program.prog.len().trailing_zeros() as usize;
            if actual == guess {
                program.min_log_committed = aggregation::MU_MIN;
                let table = cpu::layout::bytecode_table(&program.prog);
                let scalar = verifier::Bytecode::new(&table.iter().map(|word| word.0).collect::<Vec<_>>());
                let live_rows = aggregation::bytecode_rows_for(&table);
                return Context {
                    program,
                    table,
                    scalar,
                    live_rows,
                };
            }
            guess = actual;
        }
        panic!("PQTS leanSPHINCS recursive bytecode fixed point did not converge");
    })
}

/// Prepare only the fixed program and bytecode tables, without a proof or statement.
pub fn warm_up() {
    context();
}

impl Context {
    fn variables(&self) -> usize {
        self.table.len().trailing_zeros() as usize
    }

    fn deferred(&self, point: Vec<F192>) -> Result<DeferredClaim, Error> {
        aggregation::DeferredClaim::evaluate_for(point, self.variables(), self.table[0], |point| {
            let point: Vec<_> = point.iter().map(to_scalar).collect();
            from_scalar(self.scalar.evaluate(&point).expect("checked bytecode point length"))
        })
        .map_err(|_| Error::Batch("deferred point length"))
    }
}

fn claim_cells(claim: &Claim) -> Vec<F192> {
    vec![
        cell(&claim.public_key[..16]),
        cell(&claim.public_key[16..]),
        cell(&claim.message[..16]),
        cell(&claim.message[16..]),
    ]
}

fn claim_digest(claims: &[Claim]) -> [F192; 2] {
    let mut hasher = hash::Hasher::new();
    for claim in claims {
        hasher.update(&claim.public_key).update(&claim.message);
    }
    let digest = hasher.finalize();
    [cell(&digest[..16]), cell(&digest[16..])]
}

fn statement(claims: &[Claim], defer: &DeferredClaim) -> [F192; 2] {
    let seed = cpu::fs_seed(&context().program);
    let digest = claim_digest(claims);
    let header = [
        seed[0],
        seed[1],
        digest[0],
        digest[1],
        count(claims.len()),
        F192::ZERO,
        F192::ZERO,
        F192::ZERO,
    ];
    let mut hasher = hash::Hasher::new();
    for word in header {
        hasher.update(&word.c0.to_le_bytes()).update(&word.c1.to_le_bytes());
    }
    let mut cells = defer.cells();
    if !cells.len().is_multiple_of(2) {
        cells.push(F192::ZERO);
    }
    for word in cells {
        hasher
            .update(&word.c0.to_le_bytes())
            .update(&word.c1.to_le_bytes())
            .update(&word.c2.to_le_bytes());
    }
    let digest = hasher.finalize();
    [cell(&digest[..16]), cell(&digest[16..])]
}

/// Fixed framing, then every key/message in caller order. No sorting or deduplication.
pub fn public_to_bytes(claims: &[Claim]) -> Result<Vec<u8>, Error> {
    check_count(claims.len())?;
    let mut out = Vec::with_capacity(16 + 64 * claims.len());
    out.extend_from_slice(PUBLIC_MAGIC);
    out.extend_from_slice(&(claims.len() as u64).to_le_bytes());
    for claim in claims {
        out.extend_from_slice(&claim.public_key);
        out.extend_from_slice(&claim.message);
    }
    Ok(out)
}

pub fn public_from_bytes(bytes: &[u8]) -> Result<Vec<Claim>, Error> {
    if bytes.len() < 16 || bytes.len() > 16 + 64 * MAX_CLAIMS || &bytes[..8] != PUBLIC_MAGIC {
        return Err(Error::Batch("public framing"));
    }
    let n = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
    if !(1..=MAX_CLAIMS as u64).contains(&n) || bytes.len() != 16 + 64 * n as usize {
        return Err(Error::Batch("public count/length"));
    }
    bytes[16..]
        .chunks_exact(64)
        .map(|record| Claim::from_bytes(&record[..32], &record[32..]).map_err(|_| Error::Batch("claim encoding")))
        .collect()
}

fn base_hints(claims: &[Claim], children: usize) -> Hints {
    let mut hints = Hints::new();
    hints.insert("pr152_meta", vec![vec![count(claims.len()), count(children)]]);
    hints.insert("fs_seed", vec![cpu::fs_seed(&context().program).to_vec()]);
    hints.insert("signers_split", vec![list_split(claims.len())]);
    hints.insert("claims", claims.iter().map(claim_cells).collect());
    hints
}

fn leaf_hints(claims: &[Claim], signatures: &[Signature]) -> Result<(Hints, DeferredClaim), Error> {
    check_count(claims.len())?;
    if claims.len() != signatures.len() {
        return Err(Error::Batch("one raw signature per ordered claim"));
    }
    let defer = context().deferred(vec![F192::ZERO; context().variables()])?;
    let mut hints = base_hints(claims, 0);
    hints.insert("leaf_defer", vec![vec![defer.bytecode_value]]);
    // Each recovery is independent. Joining in input order preserves the witness streams.
    let items = parallel::map_collect(claims.len(), |i| advice(&claims[i], &signatures[i]));
    for mut item in items {
        item.remove("claim");
        for (name, entries) in item {
            hints.entry(name).or_default().extend(entries);
        }
    }
    Ok((hints, defer))
}

fn with_hints(hints: Hints) -> Program {
    let mut program = context().program.clone();
    for (name, entries) in hints {
        program.set_witness(name, entries);
    }
    program
}

fn recursive_hints(children: &[(&Proof, &[Claim])]) -> Result<(Vec<Claim>, Hints, DeferredClaim), Error> {
    if children.len() != 2 {
        return Err(Error::Batch("binary recursion requires exactly two children"));
    }
    for (child, expected) in children {
        child.check_statement(expected)?;
    }
    check_count(children.iter().map(|(_, claims)| claims.len()).sum())?;
    let claims: Vec<_> = children.iter().flat_map(|(_, claims)| claims.iter().cloned()).collect();
    let ctx = context();
    let mut statements = Vec::with_capacity(2);
    let mut carried = Vec::with_capacity(2);
    for (child, expected) in children {
        let defer = ctx.deferred(child.point.clone())?;
        statements.push(statement(expected, &defer));
        carried.push(defer);
    }
    let summaries = tracing::info_span!("PQTS leanSPHINCS replay children").in_scope(|| {
        parallel::map_collect(children.len(), |i| {
            verifier::replay_unchecked(
                &ctx.scalar,
                &public_input_bytes(&statements[i]),
                &scalar_proof(&children[i].0.proof),
            )
        })
    });
    let summaries = summaries.into_iter().collect::<Result<Vec<_>, _>>().map_err(|error| {
        Error::Recursion(aggregation::AggregationError::InvalidChild(
            aggregation::AggregateVerifyError::Snark(aggregation::SnarkVerifyError(error)),
        ))
    })?;
    let points: Vec<Vec<F192>> = summaries
        .iter()
        .zip(&carried)
        .flat_map(|(summary, carried)| {
            [
                summary.bytecode_point.iter().copied().map(from_scalar).collect(),
                carried.bytecode_point.clone(),
            ]
        })
        .collect();
    let sums = aggregation::bytecode_sums_for(&ctx.table, ctx.live_rows.clone(), &points);
    let mut hints = base_hints(&claims, children.len());
    let mut subproofs = Vec::with_capacity(2);
    let mut offset = 0;
    for (i, summary) in summaries.into_iter().enumerate() {
        let (child, expected) = children[i];
        hints
            .entry("pr152_child_count")
            .or_default()
            .push(vec![count(expected.len())]);
        hints.get_mut("signers_split").unwrap().push(list_split(expected.len()));
        for slot in offset..offset + expected.len() {
            hints.entry("child_claim_index").or_default().push(vec![count(slot)]);
        }
        offset += expected.len();
        hints.entry("child_defer").or_default().push(carried[i].cells());
        let (sub_hints, subproof) = aggregation::gen_verify(
            &ctx.program,
            statements[i],
            &child.proof,
            &summary,
            aggregation::bytecode_value(&sums[2 * i], &points[2 * i]),
        )
        .map_err(Error::Recursion)?;
        for (name, entry) in sub_hints {
            hints.entry(name).or_default().push(entry);
        }
        subproofs.push(subproof);
    }
    let carried: Vec<_> = carried.iter().collect();
    let (sumcheck, defer) =
        aggregation::aggregate_deferred_claims_for(&subproofs, &carried, sums, &ctx.table, ctx.live_rows.clone());
    for (name, entry) in sumcheck {
        hints.entry(name).or_default().push(entry);
    }
    Ok((claims, hints, defer))
}

/// Verify both children in the VM and carry their ordered concatenation, including duplicates.
/// Children may themselves be PQTS leanSPHINCS batch aggregates, up to MAX_CLAIMS total claims.
#[tracing::instrument(name = "PQTS leanSPHINCS recursive prove", skip_all)]
pub fn aggregate(children: &[(&Proof, &[Claim])]) -> Result<(Proof, Stats), Error> {
    tracing::info_span!("PQTS leanSPHINCS batch pool setup").in_scope(leanvm_core::init_prover);
    let (claims, hints, defer) = recursive_hints(children)?;
    let (proof, stats) =
        cpu::prove(&with_hints(hints), statement(&claims, &defer), LOG_INV_RATE).map_err(Error::Prove)?;
    Ok((
        Proof {
            count: claims.len(),
            point: defer.bytecode_point,
            proof,
        },
        stats,
    ))
}

#[cfg(test)]
#[tracing::instrument(name = "PQTS leanSPHINCS batch guest", skip_all)]
fn check_guest(claims: &[Claim], signatures: &[Signature]) -> Result<cpu::Execution, Error> {
    let (hints, defer) = leaf_hints(claims, signatures)?;
    let execution = with_hints(hints)
        .execute(statement(claims, &defer))
        .map_err(Error::Guest)?;
    if !execution.unconstrained_reads.is_empty() {
        return Err(Error::UnconstrainedReads);
    }
    Ok(execution)
}

#[tracing::instrument(name = "PQTS leanSPHINCS batch prove", skip_all)]
pub fn prove(claims: &[Claim], signatures: &[Signature]) -> Result<(Proof, Stats), Error> {
    tracing::info_span!("PQTS leanSPHINCS batch pool setup").in_scope(leanvm_core::init_prover);
    let (hints, defer) = leaf_hints(claims, signatures)?;
    let (proof, stats) =
        cpu::prove(&with_hints(hints), statement(claims, &defer), LOG_INV_RATE).map_err(Error::Prove)?;
    Ok((
        Proof {
            count: claims.len(),
            point: defer.bytecode_point,
            proof,
        },
        stats,
    ))
}

#[derive(Clone)]
pub struct Proof {
    count: usize,
    point: Vec<F192>,
    proof: cpu::Proof,
}

impl Proof {
    fn check_statement(&self, expected: &[Claim]) -> Result<(), Error> {
        check_count(expected.len())?;
        if self.count != expected.len() {
            return Err(Error::Batch("expected count"));
        }
        if self.proof.stream.get(leanvm_core::tables::N_TABLES + 1) != Some(&F192::new(LOG_INV_RATE as u64, 0, 0)) {
            return Err(Error::Batch("proof rate"));
        }
        Ok(())
    }

    pub fn to_bytes(&self) -> Result<Vec<u8>, Error> {
        let body = self.proof.to_bytes();
        if body.len() > MAX_PROOF_BYTES {
            return Err(Error::Codec("proof exceeds size limit".into()));
        }
        let mut out = Vec::with_capacity(32 + 24 * self.point.len() + body.len());
        out.extend_from_slice(PROOF_MAGIC);
        for n in [self.count, self.point.len(), body.len()] {
            out.extend_from_slice(&(n as u64).to_le_bytes());
        }
        for word in &self.point {
            for lane in [word.c0, word.c1, word.c2] {
                out.extend_from_slice(&lane.to_le_bytes());
            }
        }
        out.extend_from_slice(&body);
        Ok(out)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() < 32 || bytes.len() > MAX_PROOF_BYTES + 32 + 24 * 64 || &bytes[..8] != PROOF_MAGIC {
            return Err(Error::Batch("proof framing"));
        }
        let word = |at| u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap());
        let (n, variables, body) = (word(8), word(16), word(24));
        if !(1..=MAX_CLAIMS as u64).contains(&n) || variables > 64 || body > MAX_PROOF_BYTES as u64 {
            return Err(Error::Batch("proof count/point/body length"));
        }
        let start = 32 + 24 * variables as usize;
        if start + body as usize != bytes.len() {
            return Err(Error::Batch("proof exact length"));
        }
        let point = (32..start)
            .step_by(24)
            .map(|at| F192::new(word(at), word(at + 8), word(at + 16)))
            .collect();
        let proof =
            cpu::Proof::from_bytes(&bytes[start..]).ok_or_else(|| Error::Codec("invalid proof encoding".into()))?;
        Ok(Self {
            count: n as usize,
            point,
            proof,
        })
    }

    /// Fresh verification needs only this proof and the complete independently expected list.
    #[tracing::instrument(name = "PQTS leanSPHINCS batch verify", skip_all)]
    pub fn verify(&self, expected: &[Claim]) -> Result<(), Error> {
        self.check_statement(expected)?;
        let ctx = context();
        let defer = ctx.deferred(self.point.clone())?;
        let pi = statement(expected, &defer);
        verifier::verify_execution(&ctx.scalar, &public_input_bytes(&pi), &scalar_proof(&self.proof))
            .map(|_| ())
            .map_err(|error| Error::Verify(cpu::CpuError::Verifier(error)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reject_invalid_children(children: &[(&Proof, &[Claim])]) {
        let (claims, good, defer) = recursive_hints(children).unwrap();
        let pi = statement(&claims, &defer);
        let baseline = with_hints(good.clone()).execute(pi).unwrap();
        assert!(baseline.unconstrained_reads.is_empty());
        drop(baseline);
        for case in [
            "child-stream",
            "child-rate",
            "program-seed",
            "child-omission",
            "ordered-coverage",
            "child-count",
            "carried-bytecode",
        ] {
            let mut hints = good.clone();
            match case {
                "child-stream" => hints.get_mut("stream").unwrap()[1][leanvm_core::tables::N_TABLES + 2] += F192::ONE,
                "child-rate" => hints.get_mut("stream").unwrap()[1][leanvm_core::tables::N_TABLES + 1] += F192::ONE,
                "program-seed" => hints.get_mut("fs_seed").unwrap()[0][0] += F192::ONE,
                "child-omission" => hints.get_mut("pr152_meta").unwrap()[0][1] = count(1),
                "ordered-coverage" => hints.get_mut("child_claim_index").unwrap().swap(0, 1),
                "child-count" => hints.get_mut("pr152_child_count").unwrap()[1][0] = count(0),
                "carried-bytecode" => *hints.get_mut("child_defer").unwrap()[1].last_mut().unwrap() += F192::ONE,
                _ => unreachable!(),
            }
            assert!(
                with_hints(hints).execute(pi).is_err(),
                "{case}: invalid child witness accepted"
            );
        }
    }

    fn kat() -> (Claim, Signature) {
        (
            Claim::from_bytes(
                include_bytes!("../../../signatures/tests/pqts_lean_sphincs/kat-pk.bin"),
                include_bytes!("../../../signatures/tests/pqts_lean_sphincs/kat-message.bin"),
            )
            .unwrap(),
            Signature::from_bytes(include_bytes!(
                "../../../signatures/tests/pqts_lean_sphincs/kat-signature.bin"
            ))
            .unwrap(),
        )
    }

    #[test]
    fn public_list_preserves_count_order_and_duplicates() {
        let (a, _) = kat();
        let mut b = a.clone();
        b.message[31] ^= 1;
        let claims = vec![a.clone(), b.clone(), a.clone()];
        let bytes = public_to_bytes(&claims).unwrap();
        assert_eq!(public_from_bytes(&bytes).unwrap(), claims);
        assert_ne!(claim_digest(&claims), claim_digest(&[a.clone(), a.clone(), b]));
        assert_ne!(claim_digest(&[a.clone()]), claim_digest(&[a.clone(), a]));
        assert!(public_from_bytes(&bytes[..bytes.len() - 1]).is_err());
        let mut changed = bytes.clone();
        changed[8] = 2;
        assert!(public_from_bytes(&changed).is_err());
        changed[8] = 0;
        assert!(public_from_bytes(&changed).is_err());
        assert!(public_to_bytes(&[]).is_err());
        let claims = vec![kat().0; 512];
        let bytes = public_to_bytes(&claims).unwrap();
        assert_eq!(public_from_bytes(&bytes).unwrap(), claims);
        assert!(public_to_bytes(&vec![kat().0; 513]).is_err());
        for count in [0u64, 513] {
            let mut invalid = bytes.clone();
            invalid[8..16].copy_from_slice(&count.to_le_bytes());
            assert!(public_from_bytes(&invalid).is_err());
        }
        let mut trailing = bytes;
        trailing.push(0);
        assert!(public_from_bytes(&trailing).is_err());
    }

    #[test]
    fn repeated_n2_checks_last_raw_and_whole_public() {
        let (claim, signature) = kat();
        let claims = vec![claim.clone(), claim];
        let signatures = vec![signature.clone(), signature];
        let execution = check_guest(&claims, &signatures).unwrap();
        assert!(execution.rows()[5] >= 2 * 492);
        assert!(execution.unconstrained_reads.is_empty());
        drop(execution);
        let (good, defer) = leaf_hints(&claims, &signatures).unwrap();
        let mut changed = claims.clone();
        changed[1].message[31] ^= 1;
        assert!(with_hints(good.clone()).execute(statement(&changed, &defer)).is_err());
        changed = claims.clone();
        changed[1].public_key[31] ^= 1;
        assert!(with_hints(good.clone()).execute(statement(&changed, &defer)).is_err());
        assert!(
            with_hints(good.clone())
                .execute(statement(&claims[..1], &defer))
                .is_err()
        );
        let mut raw = *signatures[1].as_bytes();
        raw[7739] ^= 1;
        let bad = vec![signatures[0].clone(), Signature::from_bytes(&raw).unwrap()];
        let (hints, _) = leaf_hints(&claims, &bad).unwrap();
        assert!(with_hints(hints).execute(statement(&claims, &defer)).is_err());
        let mut hints = good;
        hints.get_mut("claims").unwrap()[1][0].c2 = 1;
        assert!(with_hints(hints).execute(statement(&claims, &defer)).is_err());
    }

    #[test]
    #[ignore = "generates child and recursive proofs"]
    fn same_program_two_to_one() {
        let (claim, signature) = kat();
        let claims = vec![claim.clone(), claim];
        let signatures = vec![signature.clone(), signature];
        let (left, _) = prove(&claims, &signatures).unwrap();
        let left = Proof::from_bytes(&left.to_bytes().unwrap()).unwrap();
        left.verify(&claims).unwrap();
        let children = [(&left, claims.as_slice()), (&left, claims.as_slice())];
        let (root, _) = aggregate(&children).unwrap();
        let expected = [claims.clone(), claims.clone()].concat();
        let root = Proof::from_bytes(&root.to_bytes().unwrap()).unwrap();
        root.verify(&expected).unwrap();
        assert!(root.verify(&expected[..2]).is_err());
        let mut changed = expected;
        changed[3].message[31] ^= 1;
        assert!(root.verify(&changed).is_err());
        reject_invalid_children(&children);
    }
}
