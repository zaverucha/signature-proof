// #![deny(
//     //warnings,
//     //unused,
//     future_incompatible,
//     nonstandard_style,
//     rust_2018_idioms,
//     missing_docs
//  )]
#![allow(non_snake_case)]
#![forbid(unsafe_code)]

use crate::{
    errors::NrError,
    issuance_proof::{IssuanceProof, IssuanceProofParams},
    nrproof::{NRProof, NRProofMessage, NRProofParams, SchemeType},
    types::{digest_to_F, Fp, Fq, NRCurve},
};
use ff::Field;
use merlin::Transcript;
use r1csipa::transcript::TranscriptProtocol;
//use rand::RngCore;
use halo2curves::CurveExt;
use halo2curves::{group::Curve, CurveAffine};
use rand_core::OsRng;
use rand_core::RngCore;
use serde::Serialize;
use sha2::{Digest, Sha256};

type NRPubKey = NRCurve;
pub struct NRKeyPair {
    sk: Fq,
    pub pk: NRPubKey,
}

#[derive(Clone)]
pub struct NrSig {
    pub r: Fp,
    pub s: Fq,
    pub R: NRCurve, // We store R with the signature for convenience when generating proofs. (r,s) is sufficient for verification
}

impl NRKeyPair {
    pub fn to_Fq(r: Fp) -> Fq {
        Fq::from_bytes(&r.to_bytes()).unwrap()
    }

    pub fn get_H_and_V() -> (NRCurve, NRCurve) {
        let hasher =
            <NRCurve as CurveAffine>::CurveExt::hash_to_curve("domain_prefix: NR blind signatures");
        let H: NRCurve = hasher("H".as_bytes()).into();
        let V: NRCurve = hasher("V".as_bytes()).into();

        (H, V)
    }
    pub fn get_H() -> NRCurve {
        let (H, _) = Self::get_H_and_V();
        H
    }

    pub fn generate() -> Self {
        let sk = Fq::random(OsRng);
        let pk = (NRCurve::generator() * sk).to_affine();

        Self { sk, pk }
    }

    // Create a signature (This is Scheme1 from the paper)
    pub fn sign(&self, message: &[u8]) -> NrSig {
        let digest: [u8; 32] = sha2::Sha256::digest(message).into();
        let m = digest_to_F::<Fq>(&digest);
        let Hm = Self::get_H() * m;

        let k = Fq::random(OsRng);
        let R = (Hm + (NRCurve::generator() * -k)).to_affine();
        let r = R.x;

        let s = -self.sk * Self::to_Fq(r) + k;

        NrSig { r, s, R }
    }

    // Verify a signature (Scheme1)
    pub fn verify(pk: NRPubKey, message: &[u8], signature: &NrSig) -> bool {
        let digest: [u8; 32] = sha2::Sha256::digest(message).into();
        let m = digest_to_F::<Fq>(&digest);

        Self::verify_from_field_element(pk, &m, signature)
    }

    // Verify a signature, when the message is input as a field element (Scheme 1)
    pub fn verify_from_field_element(pk: NRPubKey, message: &Fq, signature: &NrSig) -> bool {
        assert!(signature.r == signature.R.x);
        let r_fq = Self::to_Fq(signature.r);

        // Compute g^(-s) * pk^(-r) * H^m and check if its x-coordinate equals r
        let g_s = NRCurve::generator() * -signature.s;
        let pk_r = pk * (-r_fq);
        let Hm = Self::get_H() * message;
        let point = (g_s + pk_r + Hm).to_affine();

        point.x == signature.r
    }

    // Create a signature (This is Scheme2 from the paper)
    pub fn sign2(&self, message: &[u8]) -> Option<NrSig> {
        let Hm = Self::hashes_to_curve(&message.to_vec());
        Hm?;
        let Hm = Hm.unwrap();

        let k = Fq::random(OsRng);
        let R = (Hm + (NRCurve::generator() * -k)).to_affine();
        let r = R.x;

        let s = -self.sk * Self::to_Fq(r) + k;

        Some(NrSig { r, s, R })
    }

    // // Verify a signature (Scheme2)
    pub fn verify2(pk: NRPubKey, message: &[u8], signature: &NrSig) -> bool {
        assert!(signature.r == signature.R.x);
        let r_fq = Self::to_Fq(signature.r);

        // Compute g^(-s) * pk^(-r) * H(m) and check if its x-coordinate equals r
        let Hm = Self::hashes_to_curve(&message.to_vec());
        if Hm.is_none() {
            return false;
        }
        let Hm = Hm.unwrap();
        let g_s = NRCurve::generator() * -signature.s;
        let pk_r = pk * (-r_fq);
        let point = (g_s + pk_r + Hm).to_affine();

        point.x == signature.r
    }

    // Generate a random 256-bit byte string that hashes to the curve
    pub fn choose_random_message() -> Vec<u8> {
        loop {
            // Generate 32 random bytes
            let mut rng = OsRng;
            let mut message = vec![0u8; 32];
            rng.fill_bytes(&mut message);
            if Self::hashes_to_curve(&message).is_some() {
                return message;
            }
        }
    }

    // Hash a byte string to the curve by hashing with SHA-256,
    // truncating to 248-bits, casting as a field element, then
    // checking if it's the x-coordinate of a point on the curve.
    // Returns the point or none if the message doesn't hit a point.
    // We assume that applications can vary the msg (say with a
    // counter) until it hits a point.
    pub fn hashes_to_curve(msg: &Vec<u8>) -> Option<NRCurve> {
        let mut digest: [u8; 32] = Sha256::digest(msg).into();
        digest[digest.len() - 1] = 0;

        // Convert to a field element, then find y
        let x = digest_to_F::<Fp>(&digest);
        let y2: Fp = x * x * x + x * NRCurve::a() + NRCurve::b();
        if let Some(y) = y2.sqrt().into() {
            if let Some(P) = NRCurve::from_xy(x, y).into() {
                return Some(P);
            }
        }

        None
    }
}

#[derive(Serialize)]
struct PiSLProof {
    c: Fq,   // Challenge
    t_k: Fq, // Response for k
    t_m: Fq, // Response for m
}

impl PiSLProof {
    // Prove knowledge of k and m in R0 = H^m * g^(-k)
    pub fn prove(R0: &NRCurve, k: &Fq, m: &Fq) -> Self {
        // Choose random blinding factors
        let r_k = Fq::random(OsRng);
        let r_m = Fq::random(OsRng);

        // Compute commitment A = H^r_m * g^(r_k)
        let A = NRKeyPair::get_H() * r_m + NRCurve::generator() * (r_k);

        // Compute challenge c = H(R0 || A)
        let mut prover_transcript = Transcript::new(b"PiSLProof");
        prover_transcript.append_point(b"R0", R0);
        prover_transcript.append_point(b"A", &A.to_affine());
        let c = prover_transcript.challenge_scalar(b"challenge");

        // Compute responses
        let t_k = r_k + c * (-k);
        let t_m = r_m + c * m;

        Self { c, t_k, t_m }
    }

    // Verify the proof
    pub fn verify(&self, R0: &NRCurve) -> bool {
        // Reconstruct A' = (H^t_m * g^(t_k)) / R0^c
        let H = NRKeyPair::get_H();
        let g = NRCurve::generator();

        let R0_c = *R0 * -self.c;
        let H_tm = H * self.t_m;
        let g_tk = g * (self.t_k);

        let A_prime = (R0_c + H_tm + g_tk).to_affine();

        // Recompute challenge c' = H(R0 || A')
        let mut verifier_transcript = Transcript::new(b"PiSLProof");
        verifier_transcript.append_point(b"R0", R0);
        verifier_transcript.append_point(b"A", &A_prime);
        let c_prime = verifier_transcript.challenge_scalar(b"challenge");

        // Check if c == c'
        self.c == c_prime
    }
}

#[derive(Serialize)]
pub struct User1Msg {
    R0: NRCurve,
    piSL: PiSLProof,
}
pub struct UserState {
    m: Fq,
    k0: Fq,
    R0: NRCurve,
    pk: NRPubKey,
}
#[derive(Serialize)]
pub struct IssuerSignMsg {
    s1: Fq,
    R1: NRCurve,
}
pub struct BlindNrProtocols;
impl BlindNrProtocols {
    pub fn user1_msg(pk: &NRPubKey, m: &Fq) -> (User1Msg, UserState) {
        let k0 = Fq::random(OsRng);
        let R0 = (NRKeyPair::get_H() * m + NRCurve::generator() * (-k0)).to_affine();

        let user1_msg = User1Msg {
            R0,
            piSL: PiSLProof::prove(&R0, &k0, m),
        };

        let user_state = UserState {
            m: *m,
            k0,
            R0,
            pk: *pk,
        };

        (user1_msg, user_state)
    }

    pub fn issuer_sign_msg(
        keypair: &NRKeyPair,
        user1_msg: &User1Msg,
    ) -> Result<IssuerSignMsg, NrError> {
        // Verify Pi_SL proof first
        if !user1_msg.piSL.verify(&user1_msg.R0) {
            return Err(NrError::UserIssuanceProofInvalid);
        }

        // Compute R1 = G^{-k1}
        let k1 = Fq::random(OsRng);
        let R1 = NRCurve::generator() * (-k1);

        // Compute R = R0*R1
        let R = (user1_msg.R0 + R1).to_affine();

        // Compute r = R.x
        let r = R.x;
        let r_fq = NRKeyPair::to_Fq(r);

        // Compute s1 = -sk*r + k1
        let s1 = -keypair.sk * r_fq + k1;

        Ok(IssuerSignMsg {
            s1,
            R1: R1.to_affine(),
        })
    }

    /// Note the output here is NOT a blind signature -- the issuer knows R.  The `show` protocol must be run
    /// to create a proof of knowledge of the signature (this proof is the blind signature).
    pub fn user2_finalize(
        issuer_msg: &IssuerSignMsg,
        user_state: &UserState,
    ) -> Result<NrSig, NrError> {
        // Compute R = R0*R1, s = s1 + k0, then verify (R,s)
        let R = (user_state.R0 + issuer_msg.R1).to_affine();
        let r = R.x;
        let s = issuer_msg.s1 + user_state.k0;

        // Create signature
        let signature = NrSig { r, s, R };

        if !NRKeyPair::verify_from_field_element(user_state.pk, &user_state.m, &signature) {
            return Err(NrError::InvalidSignature);
        }

        Ok(signature)
    }

    pub fn user_show_scheme1(
        signature: &NrSig,
        public_key: &NRPubKey,
        message: &Fq,
        params: &NRProofParams,
    ) -> Result<NRProof, NrError> {
        // Create a zero-knowledge proof of knowledge of the signature
        let m = NRProofMessage {
            scheme: SchemeType::Scheme1,
            message_scheme1: Some(*message),
            message_scheme2: None,
        };
        let (H, V) = NRKeyPair::get_H_and_V();
        let proof = NRProof::prove(params, signature, &m, public_key, &H, &V);

        Ok(proof)
    }
    pub fn verify_show_scheme1(
        proof: &NRProof,
        public_key: &NRPubKey,
        message: &Fq,
        params: &NRProofParams,
    ) -> bool {
        let m = NRProofMessage {
            scheme: SchemeType::Scheme1,
            message_scheme1: Some(*message),
            message_scheme2: None,
        };
        let (H, V) = NRKeyPair::get_H_and_V();

        proof.verify(params, public_key, &m, &H, &V)
    }
}

#[derive(Serialize)]
pub struct User1MsgScheme2 {
    R0: NRCurve,
    pi: IssuanceProof,
}
pub struct UserStateScheme2 {
    m: Vec<u8>,
    k0: Fq,
    R0: NRCurve,
    pk: NRPubKey,
}

pub struct BlindNrProtocolsScheme2;
impl BlindNrProtocolsScheme2 {
    pub fn user1_msg(
        pk: &NRPubKey,
        m: &Vec<u8>,
        issuance_params: &IssuanceProofParams,
    ) -> (User1MsgScheme2, UserStateScheme2) {
        let k0 = Fq::random(OsRng);
        let negk0 = -k0;
        let Hm = NRKeyPair::hashes_to_curve(m).unwrap();

        let R0 = (Hm + NRCurve::generator() * (negk0)).to_affine();

        let user1_msg = User1MsgScheme2 {
            R0,
            pi: IssuanceProof::prove(issuance_params, &negk0, m, &Hm.y, &R0),
        };

        let user_state = UserStateScheme2 {
            m: m.clone(),
            k0,
            R0,
            pk: *pk,
        };

        (user1_msg, user_state)
    }

    pub fn issuer_sign_msg(
        keypair: &NRKeyPair,
        user1_msg: &User1MsgScheme2,
        issuance_params: &IssuanceProofParams,
    ) -> Result<IssuerSignMsg, NrError> {
        // Verify Pi_SL proof first
        if !user1_msg.pi.verify(issuance_params, &user1_msg.R0) {
            return Err(NrError::UserIssuanceProofInvalid);
        }

        // Compute R1 = G^{-k1}
        let k1 = Fq::random(OsRng);
        let R1 = NRCurve::generator() * (-k1);

        // Compute R = R0*R1
        let R = (user1_msg.R0 + R1).to_affine();

        // Compute r = R.x
        let r = R.x;
        let r_fq = NRKeyPair::to_Fq(r);

        // Compute s1 = -sk*r + k1
        let s1 = -keypair.sk * r_fq + k1;

        Ok(IssuerSignMsg {
            s1,
            R1: R1.to_affine(),
        })
    }

    /// Note the output here is NOT a blind signature -- the issuer knows R.  The `show` protocol must be run
    /// to create a proof of knowledge of the signature (this proof is the blind signature).
    pub fn user2_finalize(
        issuer_msg: &IssuerSignMsg,
        user_state: &UserStateScheme2,
    ) -> Result<NrSig, NrError> {
        // Compute R = R0*R1, s = s1 + k0, then verify (R,s)
        let R = (user_state.R0 + issuer_msg.R1).to_affine();
        let r = R.x;
        let s = issuer_msg.s1 + user_state.k0;

        // Create signature
        let signature = NrSig { r, s, R };

        if !NRKeyPair::verify2(user_state.pk, &user_state.m, &signature) {
            return Err(NrError::InvalidSignature);
        }

        Ok(signature)
    }

    pub fn user_show_scheme2(
        signature: &NrSig,
        public_key: &NRPubKey,
        message: &Vec<u8>,
        params: &NRProofParams,
    ) -> Result<NRProof, NrError> {
        // Create a zero-knowledge proof of knowledge of the signature
        let m = NRProofMessage {
            scheme: SchemeType::Scheme2,
            message_scheme1: None,
            message_scheme2: Some(message.clone()),
        };
        let (H, V) = NRKeyPair::get_H_and_V();
        let proof = NRProof::prove(params, signature, &m, public_key, &H, &V);

        Ok(proof)
    }

    pub fn verify_show_scheme2(
        proof: &NRProof,
        public_key: &NRPubKey,
        message: &Vec<u8>,
        params: &NRProofParams,
    ) -> bool {
        let m = NRProofMessage {
            scheme: SchemeType::Scheme2,
            message_scheme1: None,
            message_scheme2: Some(message.clone()),
        };
        let (H, V) = NRKeyPair::get_H_and_V();

        proof.verify(params, public_key, &m, &H, &V)
    }
}

#[cfg(test)]
mod tests {
    use crate::nrproof::NRProof;
    use flate2::{write::ZlibEncoder, Compression};

    use super::*;

    fn serialize_with_compression<T: serde::Serialize>(obj: &T) -> Vec<u8> {
        let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
        bincode::serialize_into(&mut encoder, &obj).unwrap();
        let obj_encoded = encoder.finish().unwrap();

        obj_encoded
    }

    fn print_size<T: serde::Serialize>(label: &str, obj: &T) {
        let ser = serialize_with_compression(obj);
        println!("{} size: {} bytes", label, ser.len());
    }

    #[test]
    fn test_keypair_generation() {
        let keypair = NRKeyPair::generate();
        // Check that the keypair is valid (not zero)
        assert!(keypair.sk != Fq::zero());
        // Check that the public key is properly computed from the secret key
        let expected_pk = (NRCurve::generator() * keypair.sk).to_affine();
        assert_eq!(keypair.pk, expected_pk);
    }

    #[test]
    fn test_signature_generation() {
        let keypair = NRKeyPair::generate();
        let message = b"test message for signature";
        let signature = keypair.sign(message);

        // Check that the signature components are not zero
        assert!(signature.r != Fp::zero());
        assert!(signature.s != Fq::zero());

        // Additional checks could be added here for verification
        // once verification functionality is implemented
        // Verify the signature is valid
        assert!(NRKeyPair::verify(keypair.pk, message, &signature));

        // Verify that an invalid message fails verification
        let wrong_message = b"wrong message";
        assert!(!NRKeyPair::verify(keypair.pk, wrong_message, &signature));

        // Test signature tampering
        let mut tampered_signature = signature;
        tampered_signature.s = Fq::random(OsRng);
        assert!(!NRKeyPair::verify(keypair.pk, message, &tampered_signature));
    }

    #[test]
    fn test_blind_signature_protocol_scheme1() {
        // Generate a keypair for the issuer
        let keypair = NRKeyPair::generate();

        // Generate parameters for proving knowledge of signatures
        let params_r1csipa = NRProof::create_params_r1csipa();
        let params_spartan = NRProof::create_params_spartan();

        // Create a message to be signed
        let message_bytes = b"blind signature test message";
        let digest: [u8; 32] = sha2::Sha256::digest(message_bytes).into();
        let m = digest_to_F::<Fq>(&digest);

        // Step 1: User generates first message
        let (user1_msg, user_state) = BlindNrProtocols::user1_msg(&keypair.pk, &m);
        print_size("S1: user1_msg", &user1_msg);

        // Step 2: Issuer processes message and returns signature share
        let issuer_msg = BlindNrProtocols::issuer_sign_msg(&keypair, &user1_msg).unwrap();
        print_size("S1: issuer_msg", &issuer_msg);

        // Step 3: User finalizes the signature
        let signature = BlindNrProtocols::user2_finalize(&issuer_msg, &user_state).unwrap();

        // Verify the resulting signature
        assert!(NRKeyPair::verify_from_field_element(
            keypair.pk, &m, &signature
        ));
        assert!(NRKeyPair::verify(keypair.pk, message_bytes, &signature));

        // Create and verify the blind signature with the r1csipa NIZK
        let blind_sig =
            BlindNrProtocols::user_show_scheme1(&signature, &keypair.pk, &m, &params_r1csipa)
                .unwrap();
        assert!(BlindNrProtocols::verify_show_scheme1(
            &blind_sig,
            &keypair.pk,
            &m,
            &params_r1csipa
        ));
        print_size("S1: user_show R1CSIPA", &blind_sig);

        // Create and verify the blind signature with the Spartan NIZK
        let blind_sig =
            BlindNrProtocols::user_show_scheme1(&signature, &keypair.pk, &m, &params_spartan)
                .unwrap();
        assert!(BlindNrProtocols::verify_show_scheme1(
            &blind_sig,
            &keypair.pk,
            &m,
            &params_spartan
        ));
        print_size("S1: user_show Spartan", &blind_sig);
    }

    #[test]
    fn test_pisl_proof() {
        // Generate a random message and blinding factor
        let m = Fq::random(OsRng);
        let k = Fq::random(OsRng);

        // Compute R0 = H^m * g^(-k)
        let R0 = (NRKeyPair::get_H() * m + NRCurve::generator() * (-k)).to_affine();

        // Create proof
        let proof = PiSLProof::prove(&R0, &k, &m);

        // Verify the proof
        assert!(proof.verify(&R0));

        // Test invalid proof (with wrong R0)
        let wrong_m = Fq::random(OsRng);
        let wrong_R0 = (NRKeyPair::get_H() * wrong_m + NRCurve::generator() * (-k)).to_affine();
        assert!(!proof.verify(&wrong_R0));
    }

    #[test]
    fn test_signature_generation_scheme2() {
        let keypair = NRKeyPair::generate();
        let message = NRKeyPair::choose_random_message();
        let signature = keypair.sign2(&message).unwrap();

        // Check that the signature components are not zero
        assert!(signature.r != Fp::zero());
        assert!(signature.s != Fq::zero());

        // Verify the signature is valid
        assert!(NRKeyPair::verify2(keypair.pk, &message, &signature));

        // Verify that a different message fails verification
        let wrong_message = b"wrong message";
        assert!(!NRKeyPair::verify2(keypair.pk, wrong_message, &signature));

        // Test signature tampering
        let mut tampered_signature = signature;
        tampered_signature.s = Fq::random(OsRng);
        assert!(!NRKeyPair::verify2(
            keypair.pk,
            &message,
            &tampered_signature
        ));
    }

    #[test]
    fn test_blind_signature_protocol_scheme2() {
        // Generate a keypair for the issuer
        let keypair = NRKeyPair::generate();

        // Generate parameters for proving knowledge of signatures
        let params_r1csipa = NRProof::create_params_r1csipa();
        let params_spartan = NRProof::create_params_spartan();

        // Step 1: User chooses message and generates issuance message
        let message = NRKeyPair::choose_random_message();
        let issuance_params = IssuanceProof::create_params();
        let (user1_msg, user_state) =
            BlindNrProtocolsScheme2::user1_msg(&keypair.pk, &message, &issuance_params);
        print_size("S2: user1_msg", &user1_msg);

        // Step 2: Issuer processes message and returns signature share
        let issuer_msg =
            BlindNrProtocolsScheme2::issuer_sign_msg(&keypair, &user1_msg, &issuance_params)
                .unwrap();
        print_size("S2: issuer_msg", &issuer_msg);

        // // Step 3: User finalizes the signature
        let signature = BlindNrProtocolsScheme2::user2_finalize(&issuer_msg, &user_state).unwrap();

        // // Verify the resulting signature
        assert!(NRKeyPair::verify2(keypair.pk, &message, &signature));

        // Create and verify the blind signature with the r1csipa NIZK
        let blind_sig = BlindNrProtocolsScheme2::user_show_scheme2(
            &signature,
            &keypair.pk,
            &message,
            &params_r1csipa,
        )
        .unwrap();
        assert!(BlindNrProtocolsScheme2::verify_show_scheme2(
            &blind_sig,
            &keypair.pk,
            &message,
            &params_r1csipa
        ));
        print_size("S2: user_show R1CSIPA", &blind_sig);

        // Create and verify the blind signature with the Spartan NIZK
        let blind_sig = BlindNrProtocolsScheme2::user_show_scheme2(
            &signature,
            &keypair.pk,
            &message,
            &params_spartan,
        )
        .unwrap();
        assert!(BlindNrProtocolsScheme2::verify_show_scheme2(
            &blind_sig,
            &keypair.pk,
            &message,
            &params_spartan
        ));
        print_size("S2: user_show Spartan", &blind_sig);
    }
}
