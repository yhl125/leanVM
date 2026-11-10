# SHAKE-128s known-answer fixture

Extracted without modification from NIST ACVP-Server commit `112690e8484dba7077709a05b1f3af58ddefdd5d`, `gen-val/json-files/SLH-DSA-sigVer-FIPS205/prompt.json`: vector set 53, group 25, test 343, external pure SHAKE-128s. `expectedResults.json` marks this case valid. The files contain the public key, message, empty context and raw signature; no secret key is included.

This one case is a regression fixture, not a complete conformance suite or a distinct-input benchmark corpus.

`tc343.public` wraps the same key, message and context in the single-record `LVMSLHC2` encoding. The public API test checks it against `batch::public_to_bytes`.
