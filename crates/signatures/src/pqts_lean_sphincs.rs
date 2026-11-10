//! The PQTS leanSPHINCS FORS/three-layer profile, distinct from upstream `lean_sphincs`.
//! Raw-signature verification for EthLib commit 4b3c7121; no signing or key generation.

use primitives::hash;

pub const PUBLIC_KEY_BYTES: usize = 32;
pub const MESSAGE_BYTES: usize = 32;
pub const SIGNATURE_BYTES: usize = 7740;
pub const HEIGHTS: [usize; 3] = [8, 8, 10];
pub const LAYER_STARTS: [usize; 3] = [4240, 5396, 6552];
pub type Digest = [u8; 16];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub public_key: [u8; PUBLIC_KEY_BYTES],
    pub message: [u8; MESSAGE_BYTES],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature([u8; SIGNATURE_BYTES]);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    PublicKeyLength,
    MessageLength,
    SignatureLength,
    DigitSum { layer: usize },
    RootMismatch,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PQTS leanSPHINCS {self:?}")
    }
}
impl std::error::Error for Error {}

impl Claim {
    pub fn from_bytes(public_key: &[u8], message: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            public_key: public_key.try_into().map_err(|_| Error::PublicKeyLength)?,
            message: message.try_into().map_err(|_| Error::MessageLength)?,
        })
    }
}

impl Signature {
    pub fn from_bytes(raw: &[u8]) -> Result<Self, Error> {
        Ok(Self(raw.try_into().map_err(|_| Error::SignatureLength)?))
    }

    pub fn as_bytes(&self) -> &[u8; SIGNATURE_BYTES] {
        &self.0
    }

    pub fn digest(&self, offset: usize) -> Digest {
        self.0[offset..offset + 16].try_into().unwrap()
    }

    pub fn counter(&self, layer: usize) -> u32 {
        let start = LAYER_STARTS[layer];
        u32::from_le_bytes(self.0[start..start + 4].try_into().unwrap())
    }
}

fn bits_le(bytes: &[u8], start: usize, count: usize) -> u32 {
    assert!(count <= 32 && start + count <= 8 * bytes.len());
    (0..count).fold(0, |out, bit| {
        out | (u32::from((bytes[(start + bit) / 8] >> ((start + bit) % 8)) & 1) << bit)
    })
}

pub fn digits(encoding: &Digest) -> [u8; 64] {
    std::array::from_fn(|i| (encoding[i / 4] >> (2 * (i % 4))) & 3)
}

fn address(tag: u8, step: u8, layer: usize, tree: u32, hi: u32, lo: u32) -> Digest {
    assert!(tag < 32 && step < 8 && layer < 3 && hi < 1 << 24);
    let mut out = [0; 16];
    out[..4].copy_from_slice(&lo.to_le_bytes());
    out[4..7].copy_from_slice(&hi.to_le_bytes()[..3]);
    out[7] = tag + 32 * step;
    out[8] = layer as u8;
    out[9..13].copy_from_slice(&tree.to_le_bytes());
    out
}

fn key(index: u32, layer: usize) -> (u32, u32) {
    let below = 8 * layer;
    (
        index >> (below + HEIGHTS[layer]),
        (index >> below) & ((1 << HEIGHTS[layer]) - 1),
    )
}

/// Computed advice, including on invalid signatures. The guest checks it independently.
pub struct Recovery {
    pub digest: [u8; 64],
    pub encodings: [Digest; 3],
    pub root: Digest,
}

struct Hashes {
    parameter: Digest,
}

impl Hashes {
    fn full(&self, addr: Digest, payload: &[u8]) -> [u8; 32] {
        hash::Hasher::new()
            .update(&self.parameter)
            .update(&addr)
            .update(payload)
            .finalize()
    }

    fn short(&self, addr: Digest, payload: &[u8]) -> Digest {
        self.full(addr, payload)[..16].try_into().unwrap()
    }
}

pub fn recover(claim: &Claim, signature: &Signature) -> Recovery {
    let hashes = Hashes {
        parameter: claim.public_key[16..].try_into().unwrap(),
    };
    let mut digest = [0; 64];
    let payload = [&claim.message[..], &signature.as_bytes()[..16]].concat();
    for call in 0..2 {
        digest[32 * call..32 * call + 32].copy_from_slice(&hashes.full(address(12, 0, 0, 0, call as u32, 0), &payload));
    }
    let index = bits_le(&digest, 0, 26);
    let mut fors = Vec::with_capacity(768);
    for tree in 0..24 {
        let leaf = bits_le(&digest, 26 + 10 * tree, 10);
        let start = 16 + 176 * tree;
        let mut node = hashes.short(
            address(15, 0, 0, 0, tree as u32 + 64 * leaf, index),
            &signature.digest(start),
        );
        for level in 0..9 {
            let sibling = signature.digest(start + 16 * (level + 1));
            let pair = if (leaf >> level) & 1 == 0 {
                [node, sibling]
            } else {
                [sibling, node]
            };
            node = hashes.short(
                address(
                    17,
                    0,
                    0,
                    0,
                    tree as u32 + 64 * ((level + 1) as u32 + 16 * (leaf >> (level + 1))),
                    index,
                ),
                &pair.concat(),
            );
        }
        let sibling = signature.digest(start + 160);
        let pair = if (leaf >> 9) & 1 == 0 {
            [node, sibling]
        } else {
            [sibling, node]
        };
        fors.extend_from_slice(&pair.concat());
    }
    let mut signed = fors;
    let mut encodings = [[0; 16]; 3];
    for layer in 0..3 {
        let (tree, leaf) = key(index, layer);
        let payload = [&signed[..], &signature.counter(layer).to_le_bytes()].concat();
        encodings[layer] = hashes.short(address(4, 0, layer, tree, 0, leaf), &payload);
        let mut ends = Vec::with_capacity(1024);
        for (chain, digit) in digits(&encodings[layer]).into_iter().enumerate() {
            let mut node = signature.digest(LAYER_STARTS[layer] + 4 + 16 * chain);
            for step in digit..3 {
                node = hashes.short(address(1, step, layer, tree, chain as u32, leaf), &node);
            }
            ends.extend_from_slice(&node);
        }
        let mut node = hashes.short(address(2, 0, layer, tree, 0, leaf), &ends);
        for level in 0..HEIGHTS[layer] {
            let sibling = signature.digest(LAYER_STARTS[layer] + 1028 + 16 * level);
            let pair = if (leaf >> level) & 1 == 0 {
                [node, sibling]
            } else {
                [sibling, node]
            };
            node = hashes.short(
                address(3, 0, layer, tree, (level + 1) as u32, leaf >> (level + 1)),
                &pair.concat(),
            );
        }
        signed = node.to_vec();
    }
    Recovery {
        digest,
        encodings,
        root: signed.try_into().unwrap(),
    }
}

pub fn verify(claim: &Claim, signature: &Signature) -> Result<Recovery, Error> {
    let recovered = recover(claim, signature);
    for (layer, encoding) in recovered.encodings.iter().enumerate() {
        if digits(encoding).into_iter().map(u32::from).sum::<u32>() != 128 {
            return Err(Error::DigitSum { layer });
        }
    }
    if recovered.root != claim.public_key[..16] {
        return Err(Error::RootMismatch);
    }
    Ok(recovered)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kat_and_canonical() {
        let pk = include_bytes!("../tests/pqts_lean_sphincs/kat-pk.bin");
        let message = include_bytes!("../tests/pqts_lean_sphincs/kat-message.bin");
        let raw = include_bytes!("../tests/pqts_lean_sphincs/kat-signature.bin");
        let claim = Claim::from_bytes(pk, message).unwrap();
        let signature = Signature::from_bytes(raw).unwrap();
        assert_eq!(signature.as_bytes(), raw);
        verify(&claim, &signature).unwrap();
        assert_eq!(Claim::from_bytes(&pk[..31], message), Err(Error::PublicKeyLength));
        assert_eq!(Claim::from_bytes(pk, &message[..31]), Err(Error::MessageLength));
        assert_eq!(Signature::from_bytes(&raw[..7739]), Err(Error::SignatureLength));
        assert_eq!(
            Signature::from_bytes(&[raw.as_slice(), &[0]].concat()),
            Err(Error::SignatureLength)
        );
        let mut other = claim.clone();
        other.message[0] ^= 1;
        assert!(verify(&other, &signature).is_err());
        let mut other = *raw;
        other[7740 - 1] ^= 1;
        assert!(verify(&claim, &Signature::from_bytes(&other).unwrap()).is_err());
    }
}
