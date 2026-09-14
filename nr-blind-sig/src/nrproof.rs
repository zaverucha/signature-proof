//! This library implements bellpepper circuits proving knowledge of NR signatures and uses Spartan or R1CS-IPA to prove them.
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

use bellpepper_core::{
    num::AllocatedNum, test_cs::TestConstraintSystem, Circuit, ConstraintSystem, SynthesisError,
};
use ff::Field;
use flate2::{write::ZlibDecoder, write::ZlibEncoder, Compression};
use halo2curves::group::Curve;
use merlin::Transcript;
use std::collections::HashMap;
use std::io::Write;

use crate::ecc::AllocatedPoint;
use crate::emulated::field_element::EmulatedFieldElement;
use crate::emulated::util::allocated_num_to_emulated_fe;
use crate::nrsig::{NRKeyPair, NrSig};
use crate::poseidon::{Poseidon, PoseidonCircuit, PoseidonConstantsCircuit};
use crate::types::{fp_to_fr, fq_to_fr, fr_to_fq, Fq, FqEmulatedParams, Fr, NRCurve, PiCurve};
use crate::utils::{enforce_equal, ff_to_big};
use ark_std::{end_timer, start_timer};
#[cfg(feature = "print-trace")]
use bellpepper_core::Comparable;
use halo2curves::group::prime::PrimeCurveAffine;
#[cfg(feature = "print-trace")]
use num_format::{Locale, ToFormattedString};
use r1csipa::r1cs::{R1CSInstance, R1CSProof, R1CSProofParams};
use r1csipa::transcript::TranscriptProtocol;
use rand_core::OsRng;
use serde::Serialize;
use spartan_t256::{
    bellpepper::solver::SatisfyingAssignment, Assignment, Instance, NIZKGens, NIZK,
};

// Proof Pi_NR (proof of a Nyberg-Rueppel signature)
// Notation
//    Y: verification key
//    r, R: signature value, r = f(R) = R.x
//    s: other signature value
//    m: message to be signed
//    V^z: random blinding value z, and extra base V
// Un-blinded verification equation:
//   H^m == R * Y^r * G^s
// Blinded verification equation:
//    R * V^z == Y^{-r} * G^{-s} * H^m * V^z    (*)
// Let B denote this group element.
// m will be public, so the verifier gets
//    B0 = Y^{-r} * G^{-s} * V^z
// and computes B = B0 * H^m
// Use a Sigma-proof to prove the remaining par of the right-hand side of (*)
//    B0 = Y^{-r} * G^{-s} * H^m * V^z
// In this proof, denote t_r the response for (-r), and c is the challenge
// Use a SNARK with \Pi_dlhash to prove the LHS:
//    B = R * V^z  AND  R.x == r
// Circuit IO:
//   public inputs:  V, B, Y, h = H(r, alpha_r), t_r, c
//   private inputs: z, r, alpha_r, R
// Circuit (mod p):
//   1. Ensure t_r == alpha_r + c * r (mod q), nonnative
//   2. Ensure h = H(r, alpha_r)
//   3. Ensure B = R * V^z
//   4. Ensure R.x = r
//

pub const R1CSIPA_PARAM_LEN: usize = 8192;
pub const NUM_ABSORBS: usize = 2;

// An internal type to represent an affine point
#[derive(Clone)]
struct Point<T> {
    x: T,
    y: T,
}
fn to_fr_pt(p: &NRCurve) -> Point<Fr> {
    Point {
        x: fp_to_fr(&p.x),
        y: fp_to_fr(&p.y),
    }
}

#[derive(Clone, PartialEq, Debug)]
enum NRProofSnarkType {
    R1csIpa,
    Spartan,
}

impl std::fmt::Display for NRProofSnarkType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NRProofSnarkType::R1csIpa => write!(f, "R1CS-IPA"),
            NRProofSnarkType::Spartan => write!(f, "Spartan"),
        }
    }
}

pub struct NRProofParams {
    poseidon_constants: PoseidonConstantsCircuit<Fr>,
    snark_type: NRProofSnarkType,
    r1csipa_params: Option<R1CSProofParams<PiCurve>>,
    spartan_params: Option<NIZKGens>,
}

#[derive(Serialize)]
pub struct NRProof {
    B0: NRCurve,
    poseidon_digest: Fr,
    challenge: Fr,
    responses: HashMap<String, Fr>,
    serialized_snark: Vec<u8>,
}

#[derive(Clone, PartialEq, Debug, Copy)]
pub enum SchemeType {
    Scheme1,
    Scheme2,
}
pub struct NRProofMessage {
    pub scheme: SchemeType,
    pub message_scheme1: Option<Fq>,
    pub message_scheme2: Option<Vec<u8>>,
}

impl NRProof {
    pub fn create_params_r1csipa() -> NRProofParams {
        let poseidon_constants = PoseidonConstantsCircuit::<Fr>::default();
        let r1csipa_params =
            R1CSProofParams::<PiCurve>::generate("params for R1CS-IPA proof", R1CSIPA_PARAM_LEN);

        NRProofParams {
            poseidon_constants,
            snark_type: NRProofSnarkType::R1csIpa,
            r1csipa_params: Some(r1csipa_params),
            spartan_params: None,
        }
    }
    pub fn create_params_spartan() -> NRProofParams {
        let poseidon_constants = PoseidonConstantsCircuit::<Fr>::default();
        let public_inputs = NRCircuitPublicInputs::default(poseidon_constants.clone());
        let circuit_verifier = NRProofCircuit::new(None, &public_inputs);

        let t = start_timer!(|| "Getting R1CS Shape");
        let mut cs = spartan_t256::bellpepper::shape_cs::ShapeCS::<Fr>::new();
        let _ = circuit_verifier.synthesize(&mut cs.namespace(|| "synthesize verifier"));
        let shape = cs.r1cs_shape();
        end_timer!(t);

        let spartan_params = NIZKGens::new(shape.num_cons, shape.num_vars, shape.num_io);

        NRProofParams {
            poseidon_constants,
            snark_type: NRProofSnarkType::Spartan,
            r1csipa_params: None,
            spartan_params: Some(spartan_params),
        }
    }

    pub fn prove(
        snark_params: &NRProofParams,
        sig: &NrSig,
        message: &NRProofMessage,
        pk: &NRCurve, // Y (public key)
        H: &NRCurve,  // Message base point
        V: &NRCurve,  // Blinding base point
    ) -> Self {
        let mut prover_transcript = Transcript::new(b"NRProof");
        let G = NRCurve::generator();

        // Generate blinding factor
        let z = Fq::random(OsRng);

        // Compute the group element related to the message
        let Hm = match message.scheme {
            SchemeType::Scheme1 => {
                let m = message.message_scheme1.unwrap();

                (H * m).to_affine()
            }
            SchemeType::Scheme2 => {
                let Hm = NRKeyPair::hashes_to_curve(message.message_scheme2.as_ref().unwrap());
                Hm.unwrap()
            }
        };

        // Compute B = Y^{-r} * G^s * H^m * V^z
        let r_fq = NRKeyPair::to_Fq(sig.r);
        let B0 = (G * (-sig.s) + pk * (-r_fq) + V * z).to_affine();
        let B = (B0 + Hm).to_affine();

        // Create sigma proof for B0
        // Generate random values for commitment
        let alpha_s = Fq::random(OsRng);
        let alpha_r = Fq::random(OsRng);
        let alpha_z = Fq::random(OsRng);

        // Create a Poseidon hash of (r, alpha_r), for the DLhash proof circuit
        let mut poseidon: Poseidon<Fr> =
            Poseidon::new(snark_params.poseidon_constants.clone(), NUM_ABSORBS);
        poseidon.absorb(fp_to_fr(&sig.r));
        poseidon.absorb(fq_to_fr(&alpha_r));
        let h = poseidon.squeeze_field_element(); // H(r, alpha_r)
        let poseidon_digest = h;

        // Compute commitment R1 = G^{alpha_s} * Y^{alpha_r} * V^{alpha_z}
        let R1 = (G * alpha_s + pk * alpha_r + V * alpha_z).to_affine();

        // Generate challenge using Fiat-Shamir heuristic
        prover_transcript.append_point(b"R1", &R1);
        prover_transcript.append_point(b"pk", pk);
        prover_transcript.append_point(b"H", H);
        prover_transcript.append_point(b"V", V);
        let challenge = prover_transcript.challenge_scalar(b"sigma challenge");

        // Compute responses
        let beta_s = alpha_s + challenge * (-sig.s);
        let beta_r = alpha_r + challenge * (-r_fq); // Note: -r for Y^{-r}
        let beta_z = alpha_z + challenge * z;

        let mut responses = HashMap::new();
        responses.insert("s".to_string(), fq_to_fr(&beta_s));
        responses.insert("r".to_string(), fq_to_fr(&beta_r));
        responses.insert("z".to_string(), fq_to_fr(&beta_z));

        let public_inputs = NRCircuitPublicInputs {
            poseidon_constants: snark_params.poseidon_constants.clone(),
            V: to_fr_pt(V),
            B: to_fr_pt(&B),
            pk: to_fr_pt(pk),
            h,
            t_r: fq_to_fr(&beta_r),
            c: fq_to_fr(&challenge),
        };
        let prover_inputs = NRCircuitProverInputs {
            z: fq_to_fr(&z),
            r: fq_to_fr(&(r_fq)),
            alpha_r: fq_to_fr(&alpha_r),
            R: Point {
                x: fp_to_fr(&sig.R.x),
                y: fp_to_fr(&sig.R.y),
            },
        };
        assert_eq!(B, (sig.R + V * z).to_affine());
        let serialized_snark = Self::create_snark(
            &mut prover_transcript,
            snark_params,
            public_inputs,
            prover_inputs,
        );

        Self {
            B0,
            poseidon_digest,
            challenge: fq_to_fr(&challenge),
            responses,
            serialized_snark,
        }
    }

    pub fn verify(
        &self,
        snark_params: &NRProofParams,
        pk: &NRCurve, // Y (public key)
        message: &NRProofMessage,
        H: &NRCurve, // Message base point
        V: &NRCurve, // Blinding base point
    ) -> bool {
        let mut verifier_transcript = Transcript::new(b"NRProof");
        let G = NRCurve::generator();

        // Compute the group element related to the message
        let Hm = match message.scheme {
            SchemeType::Scheme1 => {
                let m = message.message_scheme1.unwrap();

                (H * m).to_affine()
            }
            SchemeType::Scheme2 => {
                let Hm = NRKeyPair::hashes_to_curve(message.message_scheme2.as_ref().unwrap());
                Hm.unwrap()
            }
        };

        if self.B0.is_identity().into() {
            return false;
        }
        // Recompute B
        let B = (self.B0 + Hm).to_affine();

        // Recompute commitment R1 = ( G^alpha_s * Y^alpha_r * V^alpha_z ) / B^c
        let alpha_s = fr_to_fq(self.responses.get(&"s".to_string()).unwrap_or(&Fr::ZERO));
        let alpha_r = fr_to_fq(self.responses.get(&"r".to_string()).unwrap_or(&Fr::ZERO));
        let alpha_z = fr_to_fq(self.responses.get(&"z".to_string()).unwrap_or(&Fr::ZERO));
        let chal_fq = fr_to_fq(&self.challenge);
        let R1Prime = (G * alpha_s + pk * alpha_r + V * alpha_z - self.B0 * chal_fq).to_affine();

        // Recompute challenge and verify Sigma proof
        verifier_transcript.append_point(b"R1", &R1Prime);
        verifier_transcript.append_point(b"pk", pk);
        verifier_transcript.append_point(b"H", H);
        verifier_transcript.append_point(b"V", V);
        let expected_challenge = verifier_transcript.challenge_scalar(b"sigma challenge");

        if self.challenge != fq_to_fr(&expected_challenge) {
            return false;
        }

        // Verify snark
        let public_inputs = NRCircuitPublicInputs {
            poseidon_constants: snark_params.poseidon_constants.clone(),
            V: to_fr_pt(V),
            B: to_fr_pt(&B),
            pk: to_fr_pt(pk),
            h: self.poseidon_digest,
            t_r: *self.responses.get("r").unwrap(),
            c: self.challenge,
        };

        let result = Self::verify_snark(
            &mut verifier_transcript,
            snark_params,
            &public_inputs,
            &self.serialized_snark,
        );
        if !result {
            println!(
                "SNARK verification failed in {}",
                std::any::type_name::<Self>()
            );
            return false;
        }

        true
    }

    fn create_snark(
        prover_transcript: &mut Transcript,
        snark_params: &NRProofParams,
        public_inputs: NRCircuitPublicInputs,
        prover_inputs: NRCircuitProverInputs,
    ) -> Vec<u8> {
        let circuit_verifier = NRProofCircuit::new(None, &public_inputs);
        let circuit_prover = NRProofCircuit::new(Some(prover_inputs), &public_inputs);

        if cfg!(debug_assertions) {
            // For debug builds, synthesize with the test constraint system to find failures
            let mut cs = TestConstraintSystem::<Fr>::new();
            circuit_prover
                .clone()
                .synthesize(&mut cs.namespace(|| "build_test_vec"))
                .unwrap();

            #[cfg(feature = "print-trace")]
            {
                println!(
                    "test_nr_cs: NR circuit has {} constraints and {} aux values",
                    cs.num_constraints().to_formatted_string(&Locale::en),
                    cs.aux().len().to_formatted_string(&Locale::en)
                );
            }

            assert!(cs.is_satisfied());
        }

        prover_transcript.append_message(
            b"snark_type",
            snark_params.snark_type.to_string().as_bytes(),
        );

        let mut verifier_transcript = prover_transcript.clone();

        if snark_params.snark_type == NRProofSnarkType::R1csIpa {
            let t = start_timer!(|| "Getting R1CS Shape");
            let mut cs = r1csipa::bellpepper::shape_cs::ShapeCS::<Fr>::new();
            let _ = circuit_verifier.synthesize(&mut cs.namespace(|| "synthesize verifier"));
            let shape = cs.r1cs_shape_unpadded();
            end_timer!(t);

            let t = start_timer!(|| "Calculate witness");
            let mut cs = r1csipa::bellpepper::solver::SatisfyingAssignment::<Fr>::new();
            let _ = circuit_prover.synthesize(&mut cs.namespace(|| "calculate witness"));
            let (r, witness) = R1CSInstance::new_from_shape_with_witness(&cs, &shape);
            end_timer!(t);

            let s = start_timer!(|| "R1CS prover");
            let proof = R1CSProof::create(
                &r,
                &witness,
                snark_params.r1csipa_params.as_ref().unwrap(),
                prover_transcript,
            );
            end_timer!(s);

            let bytes = bincode::serialize(&proof).unwrap();
            #[cfg(feature = "print-trace")]
            println!("R1CSIPA proof size: {} bytes", bytes.len());

            bytes
        } else if snark_params.snark_type == NRProofSnarkType::Spartan {
            let t = start_timer!(|| "Getting R1CS Shape");
            let mut cs = spartan_t256::bellpepper::shape_cs::ShapeCS::<Fr>::new();
            let _ = circuit_verifier.synthesize(&mut cs.namespace(|| "synthesize verifier"));
            let shape = cs.r1cs_shape();
            end_timer!(t);

            let t = start_timer!(|| "Calculate witness");
            let mut cs: SatisfyingAssignment<Fr> = SatisfyingAssignment::new();
            let _ = circuit_prover.synthesize(&mut cs.namespace(|| "calculate witness"));

            let (inst, witness, inputs) = cs.r1cs_instance_and_witness(&shape);
            end_timer!(t);

            let t = start_timer!(|| "Generate NIZK proof");
            let proof = NIZK::prove(
                &inst,
                witness,
                &inputs,
                snark_params.spartan_params.as_ref().unwrap(),
                prover_transcript,
            );
            end_timer!(t);

            let t = start_timer!(|| "Verify proof");
            assert!(proof
                .verify(
                    &inst,
                    &inputs,
                    &mut verifier_transcript,
                    snark_params.spartan_params.as_ref().unwrap()
                )
                .is_ok());
            end_timer!(t);

            #[cfg(feature = "print-trace")]
            {
                let proof_str = bincode::serialize(&proof).unwrap();
                println!("Proof length, serialized by bincode: {} ", proof_str.len());
            }

            let t = start_timer!(|| "Compress proof");
            let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
            bincode::serialize_into(&mut encoder, &proof).unwrap();
            let proof_encoded = encoder.finish().unwrap();
            end_timer!(t);

            #[cfg(feature = "print-trace")]
            {
                let msg_proof_len = format!(
                    "SpartanNIZK::proof_compressed_len {:?}",
                    proof_encoded.len()
                );
                println!("{}", msg_proof_len);
            }

            proof_encoded
        } else {
            panic!("Unsupported snark type");
        }
    }

    fn verify_snark(
        verifier_transcript: &mut Transcript,
        snark_params: &NRProofParams,
        public_inputs: &NRCircuitPublicInputs,
        serialized_snark: &[u8],
    ) -> bool {
        let circuit_verifier = NRProofCircuit::new(None, public_inputs);
        verifier_transcript.append_message(
            b"snark_type",
            snark_params.snark_type.to_string().as_bytes(),
        );

        if snark_params.snark_type == NRProofSnarkType::R1csIpa {
            // R1CS-IPA verification
            let t = start_timer!(|| "Getting R1CS Shape for verification");
            let mut cs = r1csipa::bellpepper::shape_cs::ShapeCS::<Fr>::new();
            let _ = circuit_verifier.synthesize(&mut cs.namespace(|| "synthesize verifier"));
            let shape = cs.r1cs_shape_unpadded();
            end_timer!(t);

            // Deserialize the proof
            let proof: R1CSProof<PiCurve> = match bincode::deserialize(serialized_snark) {
                Ok(p) => p,
                Err(_) => return false,
            };

            // Create R1CS instance for verification (without witness)
            let r = R1CSInstance::new_from_shape(&shape, &public_inputs.inputs_vector());

            let t = start_timer!(|| "R1CS verifier");
            let result = R1CSProof::verify(
                &r,
                snark_params.r1csipa_params.as_ref().unwrap(),
                verifier_transcript,
                &proof,
            )
            .is_ok();
            end_timer!(t);

            result
        } else if snark_params.snark_type == NRProofSnarkType::Spartan {
            // Spartan verification
            let t = start_timer!(|| "Getting R1CS Shape for Spartan verification");
            let mut cs = spartan_t256::bellpepper::shape_cs::ShapeCS::<Fr>::new();
            let _ = circuit_verifier.synthesize(&mut cs.namespace(|| "synthesize verifier"));
            let shape = cs.r1cs_shape();
            end_timer!(t);

            // Decompress and deserialize the proof
            let t = start_timer!(|| "Decompress proof for verification");
            let mut decoder = ZlibDecoder::new(Vec::new());
            if decoder.write_all(serialized_snark).is_err() {
                return false;
            }
            let proof_decoded = match decoder.finish() {
                Ok(data) => data,
                Err(_) => return false,
            };
            let proof: NIZK = match bincode::deserialize(&proof_decoded) {
                Ok(p) => p,
                Err(_) => return false,
            };
            end_timer!(t);

            let t = start_timer!(|| "Converting Shape to Instance");
            let inst = match Instance::new_from_shape(&shape) {
                Ok(i) => i,
                Err(_) => return false,
            };
            end_timer!(t);

            // Create inputs Assignment; skip the first value (always 1) because Spartan adds it
            let public_inputs_bytes = public_inputs
                .inputs_vector()
                .into_iter()
                .skip(1)
                .map(|x| x.to_bytes())
                .collect::<Vec<[u8; 32]>>();
            let inputs_assign = match Assignment::new(public_inputs_bytes.as_slice()) {
                Ok(i) => i,
                Err(_) => return false,
            };
            let t = start_timer!(|| "Verify Spartan proof");
            let result = proof
                .verify(
                    &inst,
                    &inputs_assign,
                    verifier_transcript,
                    snark_params.spartan_params.as_ref().unwrap(),
                )
                .is_ok();
            end_timer!(t);

            result
        } else {
            panic!("Unsupported snark type");
        }
    }
}

#[derive(Clone)]
struct NRCircuitPublicInputs {
    poseidon_constants: PoseidonConstantsCircuit<Fr>,
    V: Point<Fr>,
    B: Point<Fr>,
    pk: Point<Fr>,
    h: Fr,
    t_r: Fr,
    c: Fr,
}
impl NRCircuitPublicInputs {
    pub fn inputs_vector(&self) -> Vec<Fr> {
        let mut inputs = Vec::new();

        // Always start with 1 to make R1CS solution nontrivial
        inputs.push(Fr::ONE);

        // Add V point (x, y, 0) where 0 indicates the point is not at infinity
        inputs.push(self.V.x);
        inputs.push(self.V.y);
        inputs.push(Fr::ZERO);

        // Add B point (x, y, 0)
        inputs.push(self.B.x);
        inputs.push(self.B.y);
        inputs.push(Fr::ZERO);

        // Add pk point (x, y, 0)
        inputs.push(self.pk.x);
        inputs.push(self.pk.y);
        inputs.push(Fr::ZERO);

        // Add scalar values
        inputs.push(self.h);
        inputs.push(self.t_r);
        inputs.push(self.c);

        // Add generator point
        let generator = NRCurve::generator();
        inputs.push(fp_to_fr(&generator.x));
        inputs.push(fp_to_fr(&generator.y));
        inputs.push(Fr::ZERO);

        inputs
    }

    pub fn default(poseidon_constants: PoseidonConstantsCircuit<Fr>) -> Self {
        let generator = to_fr_pt(&NRCurve::generator());
        Self {
            V: generator.clone(),
            B: generator.clone(),
            pk: generator.clone(),
            poseidon_constants: poseidon_constants.clone(),
            h: Fr::ONE,
            t_r: Fr::ONE,
            c: Fr::ONE,
        }
    }
}

/// Holds the prover's inputs to the NR proof circuit
#[derive(Clone)]
struct NRCircuitProverInputs {
    z: Fr,
    r: Fr,
    alpha_r: Fr,
    R: Point<Fr>,
}

/// Holds the NR proof circuit
#[derive(Clone)]
pub struct NRProofCircuit {
    prover_inputs: Option<NRCircuitProverInputs>,
    public_inputs: NRCircuitPublicInputs,
}
impl NRProofCircuit {
    fn new(
        prover_inputs: Option<NRCircuitProverInputs>,
        public_inputs: &NRCircuitPublicInputs,
    ) -> Self {
        Self {
            prover_inputs: prover_inputs.clone(),
            public_inputs: public_inputs.clone(),
        }
    }
}

impl Circuit<Fr> for NRProofCircuit {
    fn synthesize<CS: ConstraintSystem<Fr>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        // allocate public inputs V, B, pk
        let V = AllocatedPoint::alloc(
            cs.namespace(|| "V"),
            Some((self.public_inputs.V.x, self.public_inputs.V.y, false)),
        )?;
        V.inputize(cs.namespace(|| "V input"))?;
        let B = AllocatedPoint::alloc(
            cs.namespace(|| "B"),
            Some((self.public_inputs.B.x, self.public_inputs.B.y, false)),
        )?;
        B.inputize(cs.namespace(|| "B input"))?;
        let pk = AllocatedPoint::alloc(
            cs.namespace(|| "pk"),
            Some((self.public_inputs.pk.x, self.public_inputs.pk.y, false)),
        )?;
        pk.inputize(cs.namespace(|| "pk input"))?;

        // allocate public inputs h, t_r, c
        let h = AllocatedNum::alloc_input(cs.namespace(|| "poseidon hash h"), || {
            Ok(self.public_inputs.h)
        })?;

        let _t_r = AllocatedNum::alloc_input(cs.namespace(|| "response t_r"), || {
            Ok(self.public_inputs.t_r)
        })?;

        let _c =
            AllocatedNum::alloc_input(cs.namespace(|| "challenge c"), || Ok(self.public_inputs.c))?;

        // allocate generator G
        let generator = NRCurve::generator();
        let G = AllocatedPoint::alloc(
            cs.namespace(|| "G"),
            Some((fp_to_fr(&generator.x), fp_to_fr(&generator.y), false)),
        )?;
        G.inputize(cs.namespace(|| "G input"))?;

        // Allocate prover inputs (z, r, alpha_r, R)
        let to_alloc = if self.prover_inputs.is_some() {
            let pi = self.prover_inputs.clone().unwrap();
            (
                Ok(pi.z),
                Ok(pi.r),
                Ok(pi.alpha_r),
                Some((pi.R.x, pi.R.y, false)),
            )
        } else {
            (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
                None,
            )
        };
        let z = AllocatedNum::alloc(cs.namespace(|| "z"), || to_alloc.0)?;
        let r = AllocatedNum::alloc(cs.namespace(|| "r"), || to_alloc.1)?;
        let alpha_r = AllocatedNum::alloc(cs.namespace(|| "alpha_r"), || to_alloc.2)?;
        let R = AllocatedPoint::alloc(cs.namespace(|| "R"), to_alloc.3)?;

        //   1. Ensure t_r == alpha_r + c * r (mod q), using emulated arithmetic
        // Alloc t_r and c, as unchcked, since they're public
        let t_r = EmulatedFieldElement::<Fr, FqEmulatedParams>::from(
            &ff_to_big(&self.public_inputs.t_r).into(),
        )
        .allocate_field_element_unchecked(&mut cs.namespace(|| "t_r"))?;
        let c = EmulatedFieldElement::<Fr, FqEmulatedParams>::from(
            &ff_to_big(&self.public_inputs.c).into(),
        )
        .allocate_field_element_unchecked(&mut cs.namespace(|| "c"))?;
        // Convert the prover values from Fr to emulated values
        let alpha_r_fe: EmulatedFieldElement<Fr, FqEmulatedParams> =
            allocated_num_to_emulated_fe(&mut cs.namespace(|| "convert alpha_r"), &alpha_r)?;
        let r_fe: EmulatedFieldElement<Fr, FqEmulatedParams> =
            allocated_num_to_emulated_fe(&mut cs.namespace(|| "convert r"), &r)?;

        let tmp = c.neg(&mut cs.namespace(|| "-c"))?;
        let tmp = tmp.mul(&mut cs.namespace(|| "-c*r"), &r_fe)?;
        let t_r_prime = tmp.add(&mut cs.namespace(|| "alpha_r + c*(-r)"), &alpha_r_fe)?;

        EmulatedFieldElement::<Fr, FqEmulatedParams>::assert_is_equal(
            &mut cs.namespace(|| "check equality"),
            &t_r,
            &t_r_prime,
        )?;

        //   2. Ensure h = H(r, alpha_r)
        let num_absorbs = 2;
        let mut poseidon: PoseidonCircuit<Fr> =
            PoseidonCircuit::new(self.public_inputs.poseidon_constants, num_absorbs);
        poseidon.absorb(&r);
        poseidon.absorb(&alpha_r);
        let h_prime = poseidon.squeeze_field_element(&mut cs.namespace(|| "squeeze"))?;

        enforce_equal(cs.namespace(|| "ensure h == h_prime "), &h, &h_prime);

        //   3. Ensure B = R * V^z
        let V_z = V.scalar_mul(cs.namespace(|| "V^z"), &z)?;
        let Bprime = R.add(cs.namespace(|| "R * V^z"), &V_z)?;
        enforce_equal(cs.namespace(|| "check B == R * V^z"), &B.x, &Bprime.x);

        //   4. Ensure R.x = r
        enforce_equal(cs.namespace(|| "R.x == r"), &r, &R.x);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        issuance_proof::IssuanceProof,
        nrsig::*,
        types::{digest_to_F, CURVE_A},
    };

    use rand_core::RngCore;
    use sha2::Digest;

    fn generate_message(scheme: SchemeType) -> NRProofMessage {
        match scheme {
            SchemeType::Scheme1 => {
                let mut rng = OsRng;
                let mut message_bytes = vec![0u8; 32];
                rng.fill_bytes(&mut message_bytes);
                let digest: [u8; 32] = sha2::Sha256::digest(message_bytes).into();
                let m = digest_to_F::<Fq>(&digest);
                NRProofMessage {
                    scheme,
                    message_scheme1: Some(m),
                    message_scheme2: None,
                }
            }
            SchemeType::Scheme2 => {
                let m = NRKeyPair::choose_random_message();
                NRProofMessage {
                    scheme,
                    message_scheme1: None,
                    message_scheme2: Some(m),
                }
            }
        }
    }

    fn test_nr_proof_helper(snark_params: NRProofParams, scheme: SchemeType) {
        // Generate a keypair for the issuer
        let keypair = NRKeyPair::generate();
        let m = generate_message(scheme);

        // Generate a signature
        let sig = match scheme {
            SchemeType::Scheme1 => {
                let (user1_msg, user_state) =
                    BlindNrProtocols::user1_msg(&keypair.pk, &m.message_scheme1.as_ref().unwrap());
                let issuer_msg = BlindNrProtocols::issuer_sign_msg(&keypair, &user1_msg).unwrap();
                let sig = BlindNrProtocols::user2_finalize(&issuer_msg, &user_state).unwrap();
                sig
            }
            SchemeType::Scheme2 => {
                let params = IssuanceProof::create_params();
                let (user1_msg, user_state) = BlindNrProtocolsScheme2::user1_msg(
                    &keypair.pk,
                    &m.message_scheme2.as_ref().unwrap(),
                    &params,
                );
                let issuer_msg =
                    BlindNrProtocolsScheme2::issuer_sign_msg(&keypair, &user1_msg, &params)
                        .unwrap();
                let sig =
                    BlindNrProtocolsScheme2::user2_finalize(&issuer_msg, &user_state).unwrap();
                sig
            }
        };

        let (H, V) = NRKeyPair::get_H_and_V();

        // Create the NR proof
        let proof = NRProof::prove(&snark_params, &sig, &m, &keypair.pk, &H, &V);

        println!(
            "NRProof created successfully with {:?}",
            snark_params.snark_type
        );
        println!("Using curve with A = {}", CURVE_A);
        // Verify the proof
        let is_valid = proof.verify(&snark_params, &keypair.pk, &m, &H, &V);

        assert!(is_valid, "NRProof verification failed");
        println!("NRProof verified successfully");

        // Test with invalid public key (should fail)
        let wrong_keypair = NRKeyPair::generate();
        let is_invalid = proof.verify(&snark_params, &wrong_keypair.pk, &m, &H, &V);
        assert!(!is_invalid, "NRProof should fail with wrong public key");

        // Test with invalid message (should fail)
        let wrong_m = generate_message(scheme);
        let is_invalid = proof.verify(&snark_params, &keypair.pk, &wrong_m, &H, &V);
        assert!(!is_invalid, "NRProof should fail with wrong message");
    }

    #[test]
    pub fn test_nr_proof_scheme1_r1csipa() {
        let snark_params = NRProof::create_params_r1csipa();
        test_nr_proof_helper(snark_params, SchemeType::Scheme1);
    }

    #[test]
    pub fn test_nr_proof_scheme1_spartan() {
        let snark_params = NRProof::create_params_spartan();
        test_nr_proof_helper(snark_params, SchemeType::Scheme1);
    }

    #[test]
    pub fn test_nr_proof_scheme2_r1csipa() {
        let snark_params = NRProof::create_params_r1csipa();
        test_nr_proof_helper(snark_params, SchemeType::Scheme2);
    }

    #[test]
    pub fn test_nr_proof_scheme2_spartan() {
        let snark_params = NRProof::create_params_spartan();
        test_nr_proof_helper(snark_params, SchemeType::Scheme2);
    }
}
