# PQTS leanSPHINCS known-answer fixture

`kat-pk.bin`, `kat-message.bin` and `kat-signature.bin` retain the known-answer input for EthLib commit `4b3c7121a38b5ae872f4d277a9a81f0d63cb1c65`. `kat-public.bin` wraps the same public key and message in the `LVM152C2` single-record batch encoding. The public API test checks that wrapper against `batch::public_to_bytes`.

`LICENSE.EthLib` preserves the fixture's source license. The signature is public test data. It is not a distinct-input benchmark corpus.
