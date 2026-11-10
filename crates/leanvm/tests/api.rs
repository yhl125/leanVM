use leanvm::*;

const MSG_0: lean_xmss::Message = [0; lean_xmss::MESSAGE_LEN];
const MSG_1: lean_xmss::Message = [1; lean_xmss::MESSAGE_LEN];
const MSG_2: lean_xmss::Message = [2; lean_xmss::MESSAGE_LEN];

#[test]
fn public_api_end_to_end() {
    setup();

    // 1. Eight leanXMSS signatures over three messages, three of the first, four of the second, one of the third,
    //    by four keys. A key signs each message at its own leaf index, which the statement does not record.
    let keys: Vec<_> = (0..4).map(|_| lean_xmss::key_gen()).collect();
    let mut lean_xmss_input = Vec::new();
    for (leaf_index, (message, count)) in (7..).zip([(MSG_0, 3), (MSG_1, 4), (MSG_2, 1)]) {
        for (secret_key, pub_key) in &keys[..count] {
            let signature = lean_xmss::sign(secret_key, &message, leaf_index).unwrap();
            lean_xmss_input.push((*pub_key, message, signature));
        }
    }

    // 2. Three leanSPHINCS signatures, each on its own message
    let mut lean_sphincs_input = Vec::new();
    for signer in 0..3u8 {
        let (secret_key, pub_key) = lean_sphincs::key_gen();
        let message = [signer; lean_sphincs::MESSAGE_LEN];
        let signature = lean_sphincs::sign(&secret_key, &message).unwrap();
        lean_sphincs_input.push((pub_key, message, signature));
    }

    // 3. Two leaves, then a root over both. Both leaves hold claims on the second message; the root's claims are the union.
    let blobs: Vec<_> = (0..lean_da::BLOB_SYMBOLS).map(|i| i as u64).collect();
    let (commitment, _) = lean_da::commit(&blobs).unwrap();
    let left = aggregate(
        &[],
        lean_xmss_input[..4].to_vec(),
        lean_sphincs_input[..1].to_vec(),
        &blobs,
        None,
        2,
    )
    .unwrap();
    let left = EthereumProof::from_proof_bytes(&left.proof_bytes(), left.claims().clone()).unwrap();
    left.verify().unwrap();
    assert_eq!(left.claims().da_commitment, Some(commitment));
    let other_blobs: Vec<_> = blobs.iter().map(|x| x ^ 42).collect();
    let (other_commitment, _) = lean_da::commit(&other_blobs).unwrap();
    let right = aggregate(
        &[],
        lean_xmss_input[4..7].to_vec(),
        lean_sphincs_input[1..].to_vec(),
        &other_blobs,
        None,
        2,
    )
    .unwrap();
    assert_eq!(right.claims().da_commitment, Some(other_commitment));
    // A proof carries one blob matrix: the root passes on one child's, by default the first's.
    let root = aggregate(&[left, right], lean_xmss_input[7..].to_vec(), vec![], &[], None, 2).unwrap();
    assert_eq!(root.claims().num_signature_claims(), 11);
    assert_eq!(root.claims().da_commitment, Some(commitment));

    // 4. Onto the wire, which carries no claims: the receiver supplies the claims it expects, and
    //    verifying says exactly these pubkeys signed exactly these messages.
    let bytes = root.proof_bytes();
    let received = EthereumProof::from_proof_bytes(&bytes, root.claims().clone()).unwrap();
    received.verify().unwrap();
    let on = |message| received.claims().xmss.iter().filter(|(_, m)| *m == message).count();
    assert_eq!((on(MSG_0), on(MSG_1), on(MSG_2)), (3, 4, 1));
    // Claims the proof does not prove fail, here one signature claim short.
    let mut fewer = root.claims().clone();
    fewer.xmss.pop();
    let wrong = EthereumProof::from_proof_bytes(&bytes, fewer).unwrap();
    assert!(matches!(wrong.verify(), Err(AggregateVerifyError::Snark(_))));

    // 5. Removing some signatures from the aggregate: `declare` is what we keep. Here every claim on MSG_1 goes,
    //    and one leanSPHINCS claim.
    let retained = EthereumClaims {
        xmss: received
            .claims()
            .xmss
            .iter()
            .filter(|(_, m)| *m != MSG_1)
            .cloned()
            .collect(),
        lean_sphincs: received.claims().lean_sphincs[1..].to_vec(),
        da_commitment: Some(commitment),
    };
    let narrowed = aggregate(&[received], vec![], vec![], &[], Some(&retained), 2).unwrap();
    narrowed.verify().unwrap();
    assert_eq!(narrowed.claims(), &retained);
    assert_eq!(narrowed.claims().num_signature_claims(), 11 - 4 - 1);

    // And the blob claim.
    let without_blobs = EthereumClaims {
        da_commitment: None,
        ..retained
    };
    let dropped = aggregate(&[narrowed], vec![], vec![], &[], Some(&without_blobs), 2).unwrap();
    dropped.verify().unwrap();
    assert_eq!(dropped.claims(), &without_blobs);
}

#[test]
#[ignore = "generates a signature proof"]
fn pqts_lean_sphincs_batch() {
    use leanvm::pqts_lean_sphincs::{Claim, Signature, SignatureError, batch};
    assert_eq!(Claim::from_bytes(&[], &[0; 32]), Err(SignatureError::PublicKeyLength));
    let claim = Claim::from_bytes(
        include_bytes!("../../signatures/tests/pqts_lean_sphincs/kat-pk.bin"),
        include_bytes!("../../signatures/tests/pqts_lean_sphincs/kat-message.bin"),
    )
    .unwrap();
    let signature = Signature::from_bytes(include_bytes!(
        "../../signatures/tests/pqts_lean_sphincs/kat-signature.bin"
    ))
    .unwrap();
    let public = include_bytes!("../../signatures/tests/pqts_lean_sphincs/kat-public.bin");
    let mut claims = batch::public_from_bytes(public).unwrap();
    assert_eq!(claims, [claim]);
    assert_eq!(batch::public_to_bytes(&claims).unwrap().as_slice(), public.as_slice());
    let (proof, _) = batch::prove(&claims, &[signature]).unwrap();
    let bytes = proof.to_bytes().unwrap();
    assert!(batch::Proof::from_bytes(&bytes[..bytes.len() - 1]).is_err());
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(batch::Proof::from_bytes(&trailing).is_err());
    let mut wrong_version = bytes.clone();
    wrong_version[0] ^= 1;
    assert!(batch::Proof::from_bytes(&wrong_version).is_err());
    let proof = batch::Proof::from_bytes(&bytes).unwrap();
    proof.verify(&claims).unwrap();
    claims[0].message[0] ^= 1;
    assert!(proof.verify(&claims).is_err());
}
