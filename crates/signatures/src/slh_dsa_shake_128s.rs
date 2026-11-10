//! FIPS 205 external-pure SLH-DSA-SHAKE-128s verification.
//! Raw-signature verification for the external pure interface; no signer.

use primitives::hash::keccak_f;

pub const PUBLIC_KEY_BYTES: usize = 32;
pub const SIGNATURE_BYTES: usize = 7856;
pub const MAX_MESSAGE_BYTES: usize = 8192;
pub type Digest = [u8; 16];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub public_key: [u8; PUBLIC_KEY_BYTES],
    pub message: Vec<u8>,
    pub context: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature([u8; SIGNATURE_BYTES]);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    PublicKeyLength,
    MessageLength,
    ContextLength,
    SignatureLength,
    RootMismatch,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SLH-DSA-SHAKE-128s {self:?}")
    }
}
impl std::error::Error for Error {}

impl Claim {
    pub fn from_bytes(pk: &[u8], message: &[u8], context: &[u8]) -> Result<Self, Error> {
        let public_key = pk.try_into().map_err(|_| Error::PublicKeyLength)?;
        if message.len() > MAX_MESSAGE_BYTES {
            return Err(Error::MessageLength);
        }
        if context.len() > 255 {
            return Err(Error::ContextLength);
        }
        Ok(Self {
            public_key,
            message: message.to_vec(),
            context: context.to_vec(),
        })
    }
    pub fn validate(&self) -> Result<(), Error> {
        if self.message.len() > MAX_MESSAGE_BYTES {
            return Err(Error::MessageLength);
        }
        if self.context.len() > 255 {
            return Err(Error::ContextLength);
        }
        Ok(())
    }
    pub fn external_message(&self) -> Vec<u8> {
        let mut message = Vec::with_capacity(2 + self.context.len() + self.message.len());
        message.extend_from_slice(&[0, self.context.len() as u8]);
        message.extend_from_slice(&self.context);
        message.extend_from_slice(&self.message);
        message
    }
}
impl Signature {
    pub fn from_bytes(raw: &[u8]) -> Result<Self, Error> {
        Ok(Self(raw.try_into().map_err(|_| Error::SignatureLength)?))
    }
    pub fn as_bytes(&self) -> &[u8; SIGNATURE_BYTES] {
        &self.0
    }
    pub fn node(&self, offset: usize) -> Digest {
        self.0[offset..offset + 16].try_into().unwrap()
    }
}

/// SHAKE256 over the existing Keccak-f primitive, including multi-block squeezing.
fn shake256<const N: usize>(message: &[u8]) -> [u8; N] {
    let mut state = [0u64; 25];
    let mut chunks = message.chunks_exact(136);
    for block in chunks.by_ref() {
        for (lane, bytes) in state.iter_mut().zip(block.chunks_exact(8)) {
            *lane ^= u64::from_le_bytes(bytes.try_into().unwrap());
        }
        keccak_f(&mut state);
    }
    let tail = chunks.remainder();
    for (i, byte) in tail.iter().enumerate() {
        state[i / 8] ^= u64::from(*byte) << (8 * (i % 8));
    }
    state[tail.len() / 8] ^= 0x1f << (8 * (tail.len() % 8));
    state[16] ^= 1 << 63;
    keccak_f(&mut state);
    let mut out = [0; N];
    for (block, bytes) in out.chunks_mut(136).enumerate() {
        if block != 0 {
            keccak_f(&mut state);
        }
        for (i, byte) in bytes.iter_mut().enumerate() {
            *byte = (state[i / 8] >> (8 * (i % 8))) as u8;
        }
    }
    out
}

fn address(layer: u32, tree: u64, kind: u32, key: u32, chain_height: u32, hash_index: u32) -> [u8; 32] {
    let mut a = [0; 32];
    a[..4].copy_from_slice(&layer.to_be_bytes());
    a[8..16].copy_from_slice(&tree.to_be_bytes());
    for (i, word) in [kind, key, chain_height, hash_index].iter().enumerate() {
        a[16 + 4 * i..20 + 4 * i].copy_from_slice(&word.to_be_bytes());
    }
    a
}

pub fn digits(message: &Digest) -> [u8; 35] {
    let mut out = [0; 35];
    let mut checksum = 0u16;
    for i in 0..32 {
        out[i] = (message[i / 2] >> (4 * (1 - i % 2))) & 15;
        checksum += u16::from(15 - out[i]);
    }
    out[32] = (checksum >> 8) as u8;
    out[33] = ((checksum >> 4) & 15) as u8;
    out[34] = (checksum & 15) as u8;
    out
}

pub struct Recovery {
    pub digest: [u8; 32],
    pub signed: [Digest; 7],
    pub root: Digest,
}

/// Advice computation has no acceptance gate; the VM recomputes the relation.
pub fn recover(claim: &Claim, signature: &Signature) -> Recovery {
    let message = [&signature.0[..16], &claim.public_key[..], &claim.external_message()].concat();
    let digest = shake256::<32>(&message);
    let hash = |addr: [u8; 32], payload: &[u8]| shake256::<16>(&[&claim.public_key[..16], &addr, payload].concat());
    let mut tree_bytes = [0; 8];
    tree_bytes[1..].copy_from_slice(&digest[21..28]);
    let mut tree = u64::from_be_bytes(tree_bytes) & ((1 << 54) - 1);
    let mut leaf = u32::from(u16::from_be_bytes(digest[28..30].try_into().unwrap())) & 511;
    let mut roots = Vec::with_capacity(224);
    for i in 0..14 {
        let mut index = 0u32;
        for j in 0..12 {
            let bit = 12 * i + j;
            index = (index << 1) | u32::from((digest[bit / 8] >> (7 - bit % 8)) & 1);
        }
        let start = 16 + i * 208;
        let mut node = hash(
            address(0, tree, 3, leaf, 0, ((i as u32) << 12) + index),
            &signature.node(start),
        );
        for level in 0..12 {
            let sibling = signature.node(start + 16 * (level + 1));
            let pair = if (index >> level) & 1 == 0 {
                [node, sibling]
            } else {
                [sibling, node]
            };
            node = hash(
                address(
                    0,
                    tree,
                    3,
                    leaf,
                    (level + 1) as u32,
                    (((i as u32) << 12) + index) >> (level + 1),
                ),
                &pair.concat(),
            );
        }
        roots.extend_from_slice(&node);
    }
    let mut node = hash(address(0, tree, 4, leaf, 0, 0), &roots);
    let mut signed = [[0; 16]; 7];
    for layer in 0..7 {
        signed[layer] = node;
        let start = 2928 + 704 * layer;
        let mut tips = Vec::with_capacity(560);
        for (chain, digit) in digits(&node).into_iter().enumerate() {
            let mut tip = signature.node(start + 16 * chain);
            for step in digit..15 {
                tip = hash(
                    address(layer as u32, tree, 0, leaf, chain as u32, u32::from(step)),
                    &tip,
                );
            }
            tips.extend_from_slice(&tip);
        }
        node = hash(address(layer as u32, tree, 1, leaf, 0, 0), &tips);
        for level in 0..9 {
            let sibling = signature.node(start + 560 + 16 * level);
            let pair = if (leaf >> level) & 1 == 0 {
                [node, sibling]
            } else {
                [sibling, node]
            };
            node = hash(
                address(layer as u32, tree, 2, 0, (level + 1) as u32, leaf >> (level + 1)),
                &pair.concat(),
            );
        }
        leaf = (tree & 511) as u32;
        tree >>= 9;
    }
    Recovery {
        digest,
        signed,
        root: node,
    }
}

pub fn verify(claim: &Claim, signature: &Signature) -> Result<Recovery, Error> {
    claim.validate()?;
    let recovered = recover(claim, signature);
    if recovered.root != claim.public_key[16..] {
        return Err(Error::RootMismatch);
    }
    Ok(recovered)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn acvp_known_answer_and_input_bounds() {
        let claim = Claim::from_bytes(
            include_bytes!("../tests/slh_dsa_shake_128s/tc343.pk"),
            include_bytes!("../tests/slh_dsa_shake_128s/tc343.message"),
            include_bytes!("../tests/slh_dsa_shake_128s/tc343.context"),
        )
        .unwrap();
        let mut raw = *include_bytes!("../tests/slh_dsa_shake_128s/tc343.signature");
        verify(&claim, &Signature::from_bytes(&raw).unwrap()).unwrap();
        assert_eq!(
            Claim::from_bytes(&claim.public_key[..31], &claim.message, &[]),
            Err(Error::PublicKeyLength)
        );
        assert_eq!(
            Claim::from_bytes(&claim.public_key, &[0; MAX_MESSAGE_BYTES + 1], &[]),
            Err(Error::MessageLength)
        );
        assert_eq!(
            Claim::from_bytes(&claim.public_key, &claim.message, &[0; 256]),
            Err(Error::ContextLength)
        );
        assert_eq!(
            Signature::from_bytes(&raw[..SIGNATURE_BYTES - 1]),
            Err(Error::SignatureLength)
        );
        let mut framed = claim.clone();
        framed.context = vec![1, 2, 3];
        assert_eq!(&framed.external_message()[..5], &[0, 3, 1, 2, 3]);
        assert_eq!(&framed.external_message()[5..], claim.message.as_slice());
        raw[7855] ^= 1;
        assert!(verify(&claim, &Signature::from_bytes(&raw).unwrap()).is_err());
    }
}
