use std::path::Path;

use crate::signature_batch::{read_bounded, report};
use bench::Plan;
use rec_aggregation::pqts_lean_sphincs::{Signature, batch};
use signatures::pqts_lean_sphincs::SIGNATURE_BYTES;

pub fn run(
    public: &Path,
    signatures: &Path,
    log_inv_rate: usize,
    plan: Plan,
) -> Result<(), Box<dyn std::error::Error>> {
    if log_inv_rate != batch::LOG_INV_RATE {
        return Err("this proof profile requires --log-inv-rate 1".into());
    }
    let claims = batch::public_from_bytes(&read_bounded(
        std::fs::File::open(public)?,
        16 + 64 * batch::MAX_CLAIMS,
    )?)?;
    let raw = read_bounded(std::fs::File::open(signatures)?, claims.len() * SIGNATURE_BYTES)?;
    if raw.len() != claims.len() * SIGNATURE_BYTES {
        return Err("expected one raw signature per public claim, in the same order".into());
    }
    let signatures = raw
        .chunks_exact(SIGNATURE_BYTES)
        .map(Signature::from_bytes)
        .collect::<Result<Vec<_>, _>>()?;
    drop(raw);
    batch::warm_up();

    let trace_span = tracing::info_span!("PQTS leanSPHINCS", count = claims.len()).entered();
    let ((proof, stats), prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        batch::prove(&claims, &signatures).expect("signature batch proves")
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        proof.verify(&claims).expect("signature batch verifies")
    });
    drop(trace_span);

    report(
        "PQTS leanSPHINCS",
        claims.len(),
        &stats,
        proof.to_bytes()?.len(),
        &prove_time,
        &verify_time,
    );
    Ok(())
}
