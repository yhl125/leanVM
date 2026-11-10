# PQTS leanSPHINCS on leanVM

`leanvm::pqts_lean_sphincs` verifies the PQTS leanSPHINCS profile pinned to EthLib commit `4b3c7121a38b5ae872f4d277a9a81f0d63cb1c65`. It has a 32-byte public key, 32-byte message and 7740-byte raw signature. It is distinct from leanVM's current `lean_sphincs` and from standard SLH-DSA. The two leanSPHINCS profiles share tree heights and signature length but use different address formats, public-key ordering and message hashes. Their keys and signatures are not interchangeable.

## API

`Claim::from_bytes` and `Signature::from_bytes` decode inputs. `verify_signature` runs native signature verification. `prove` handles one claim; `batch::prove` handles 1 through 512 ordered claims. `batch::Proof::verify` takes the complete expected list. `batch::aggregate` verifies exactly two child proofs in the VM and carries their ordered concatenation under the same program and profile.

Every signature is checked. Ordered duplicates remain part of the statement. Verification hashes the expected list, so input processing remains linear in its length. A proof establishes the existence of valid signatures for the claims, not the identity of externally designated signature bytes. Proofs are not zero knowledge.

## Input files

`public.bin` is `LVM152C2`, a little-endian `u64` count, then each 32-byte key and 32-byte message in order. `batch::public_to_bytes` and `batch::public_from_bytes` provide the codec. `signatures.bin` contains the matching raw 7740-byte signatures concatenated in the same order. Input lengths, counts and trailing bytes are checked.

## Benchmark

The CLI uses the same `bench::Plan`, jemalloc and thread pool as `aggregate --sphincs`. N is the number of signatures in the input list; `--repeat` is the number of measured proving calls. Leave `--tracing` off for quoted benchmark timings and use it separately to inspect phases. `LEANVM_NUM_THREADS` keeps its upstream meaning.

The checked-in known-answer fixture gives an N=1 smoke run:

```sh
cargo leanvm pqts-lean-sphincs crates/signatures/tests/pqts_lean_sphincs/kat-public.bin crates/signatures/tests/pqts_lean_sphincs/kat-signature.bin --repeat 3
```

For larger batches, encode the public list with `batch::public_to_bytes` and supply the matching concatenated raw signatures. The input file determines N. Counts from 1 through 512 are supported. Repeating a known-answer fixture is useful for regression checks; throughput measurements should identify the dataset used.

Input decoding and program preparation precede measurement. `Plan` discards one proving warmup, then reports the mean and spread over `--repeat` full proving calls, including advice generation. The final proof is verified `--repeat` times in the same process, with zero verification cooldown. Proof encoding is outside these timings.

Peak memory covers the whole process: setup, warmup, all proving and verification calls, and allocator retention. It is not per-proof memory. Historical measurements from the research harness retain their original measurement scope.

The current proof profile requires `--log-inv-rate 1`; other values are rejected.

## Compatibility and tests

The input codec `LVM152C2` and signature relation retain their original meanings. Proofs now use leanVM's native canonical codec under `LVPQTP01` (single) and `LVPQTB01` (batch), replacing the old bincode transport. The MAX512 guest has its own compiled program identity; old proofs and child proofs must be regenerated. Historical domains and hint names containing `pr152` remain internal identifiers.

The small EthLib known-answer fixture, guest witness checks, list codec checks and ignored full recursive check remain. Runtime diagnostic commands and the separate warm-harness test are omitted. Run VM tests in release mode; the normal leanVM testing conventions apply. No dependency, core verifier or security parameter is changed by the naming and benchmark integration.


Run the focused checks with the existing Cargo test targets:

```sh
cargo test --release -p signatures pqts_lean_sphincs -- --test-threads=1
cargo test --release -p rec_aggregation pqts_lean_sphincs -- --test-threads=1
cargo test --release -p leanvm --test api pqts_lean_sphincs_batch -- --ignored
cargo test --release -p rec_aggregation pqts_lean_sphincs::batch::tests::same_program_two_to_one -- --exact --ignored
```

The last check proves two children recursively, including repeated claims. These additions do not inherit the current upstream leanSPHINCS formal statements. The repository contains verification and proving APIs, not a production signer or a complete security audit.
