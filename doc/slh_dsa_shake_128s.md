# SLH-DSA-SHAKE-128s on leanVM

`leanvm::slh_dsa_shake_128s` implements the FIPS 205 external pure SHAKE-128s verification interface and proves that verification in leanVM. Public keys are 32 bytes and signatures are 7856 bytes. This API supports messages up to 8192 bytes and contexts up to 255 bytes. It does not implement signing, prehash mode or SHA2 parameter sets.

## API

`Claim::from_bytes(pk, message, context)` and `Signature::from_bytes` validate input lengths. `verify_signature` performs native verification; `prove` and `Proof::verify` prove and verify the single-claim guest. `batch::prove` and `batch::Proof::verify` handle 1 through 128 ordered claims with a common message/context length shape.

The guest computes external `0x00 || context_length || context || message` framing, Hmsg, FORS, WOTS+ and the hypertree relation. Both host and guest bind the full expected inputs to the public statement. The batch binds count and order, and constrains unused digest slots to zero. Verification processes the full expected list. Proofs establish the existence of valid signatures and are not zero knowledge.

Program preparation retains only the most recent message/context length shape for each of the single and batch APIs. Callers do not need a cache manager. Alternating shapes can recompile; `warm_up` prepares the selected shape before measurement.

## Input files

`public.bin` is `LVMSLHC2`, a little-endian `u64` count, then each key, `u64 context_len`, `u64 message_len`, context and message. `batch::public_to_bytes` and `batch::public_from_bytes` provide the codec. `signatures.bin` contains exactly one raw 7856-byte signature per claim in the same order. Counts, field lengths and trailing bytes are checked.

## Benchmark

The CLI uses the same `bench::Plan`, jemalloc and thread pool as `aggregate --sphincs`. N is the number of signatures in the input list; `--repeat` is the number of measured proving calls. Leave `--tracing` off for quoted benchmark timings and use it separately to inspect phases. `LEANVM_NUM_THREADS` keeps its upstream meaning.

The checked-in known-answer fixture gives an N=1 smoke run:

```sh
cargo leanvm slh-dsa-shake-128s crates/signatures/tests/slh_dsa_shake_128s/tc343.public crates/signatures/tests/slh_dsa_shake_128s/tc343.signature --repeat 3
```

For larger batches, encode the public list with `batch::public_to_bytes` and supply the matching concatenated raw signatures. The input file determines N. Counts from 1 through 128 are supported. Repeating a known-answer fixture is useful for regression checks; throughput measurements should identify the dataset used.

Input decoding and program preparation precede measurement. `Plan` discards one proving warmup, then reports the mean and spread over `--repeat` full proving calls, including advice generation. The final proof is verified `--repeat` times in the same process, with zero verification cooldown. Proof encoding is outside these timings.

Peak memory covers the whole process: setup, warmup, all proving and verification calls, and allocator retention. It is not per-proof memory. Historical measurements from the research harness retain their original measurement scope.

The current proof profile requires `--log-inv-rate 1`; other values are rejected.

## Compatibility and tests

The `SLH-SHAKE128s-v1` statement domain and signature relation are retained. Proofs now use leanVM's native canonical codec under `LVSHKP01` (single) and `LVSHKB01` (batch), replacing the old bincode transport. Proofs from the older VM must be regenerated. This module does not import the PQTS profile, and it does not provide recursive aggregation. The existing codec test and one extracted NIST ACVP known-answer case cover native verification, guest binding and malformed advice. These are regression tests, not complete conformance or security certification.


Run the focused checks with the existing Cargo test targets:

```sh
cargo test --release -p signatures slh_dsa_shake_128s -- --test-threads=1
cargo test --release -p rec_aggregation slh_dsa_shake_128s -- --test-threads=1
cargo test --release -p leanvm --test api slh_dsa_shake_128s_batch -- --ignored
```

The API count limit is not a measured memory guarantee. Use a small-to-large admission sequence for a new machine or VM revision. The upstream Lean statements do not cover this SHAKE guest.
