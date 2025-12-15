//! Issuance proof circuits for blind NR signatures
#![allow(non_snake_case)]
#![forbid(unsafe_code)]

use crate::ecc::AllocatedPoint;
use crate::types::{fp_to_fr, fq_to_fr, Fp, Fq, Fr, NRCurve};
use crate::utils::{self, enforce_equal};
use ark_std::{end_timer, start_timer};
use bellpepper::gadgets::sha256::sha256;
use bellpepper_core::boolean::{AllocatedBit, Boolean};
use bellpepper_core::{num::AllocatedNum, Circuit, ConstraintSystem, SynthesisError};
use ff::Field;
use flate2::{write::ZlibDecoder, write::ZlibEncoder, Compression};
use merlin::Transcript;
use serde::Serialize;
use spartan_t256::bellpepper::r1cs::R1CSShape;
use spartan_t256::{
    bellpepper::solver::SatisfyingAssignment, Assignment, Instance, NIZKGens, NIZK,
};
use std::io::Write;

// Proof Pi_Sl for issuance of an NR-blind signature with Scheme 2
// Notation:
// R0: group element sent from user to issuer
// k0: user-chosen random value
// m : user-chosen message to be signed.  Must fit in Fr
// Prover inputs: k0, m, H.y  (k0, m in NRCurve::Scalar, H.y in NRCurve::Base)
// Public inputs: R0, G (in NRCurve::Base)
// Circuit:
//    H.x = HashToField(m)
//        HashToField: hashes m with SHA-256 and takes the first 248 bits of the digest as a field element
//    Ensure H = (H.x, H.y) is on the curve
//    R0 = H * G^k0

// Constants
const MSG_LEN_BITS: usize = 32; // The circuit needs to have a fixed message length

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

pub struct IssuanceProofParams {
    spartan_params: NIZKGens,
    shape: R1CSShape<Fr>,
}

#[derive(Serialize)]
pub struct IssuanceProof {
    serialized_snark: Vec<u8>,
}

impl IssuanceProof {
    pub fn create_params() -> IssuanceProofParams {
        let t_params = start_timer!(|| "Creating issuance proof params");
        let public_inputs = IssuanceCircuitPublicInputs::default();
        let circuit_verifier = IssuanceProofCircuit::new(None, &public_inputs);

        let t = start_timer!(|| "Getting R1CS Shape");
        let mut cs = spartan_t256::bellpepper::shape_cs::ShapeCS::<Fr>::new();
        let _ = circuit_verifier.synthesize(&mut cs.namespace(|| "synthesize verifier"));
        let shape = cs.r1cs_shape();
        end_timer!(t);

        let t = start_timer!(|| "Creating Spartan generators");
        let spartan_params = NIZKGens::new(shape.num_cons, shape.num_vars, shape.num_io);
        end_timer!(t);

        end_timer!(t_params);

        IssuanceProofParams {
            spartan_params,
            shape,
        }
    }

    pub fn prove(
        params: &IssuanceProofParams,
        negk0: &Fq,
        m: &Vec<u8>,
        y: &Fp,
        R0: &NRCurve,
    ) -> Self {
        // Build public inputs
        let R0_pt = to_fr_pt(R0);
        let public_inputs = IssuanceCircuitPublicInputs { R0: R0_pt };

        // Build prover inputs
        let prover_inputs = IssuanceCircuitProverInputs {
            negk0: fq_to_fr(negk0),
            m: m.clone(),
            y: fp_to_fr(y),
        };

        // Create circuit for proving
        let circuit = IssuanceProofCircuit::new(Some(prover_inputs.clone()), &public_inputs);

        // Calculate the witness
        let mut cs: SatisfyingAssignment<Fr> = SatisfyingAssignment::new();
        circuit.synthesize(&mut cs.namespace(|| "witness")).unwrap();
        let (inst, witness, inputs) = cs.r1cs_instance_and_witness(&params.shape);

        // Generate the NIZK proof
        let mut prover_transcript = Transcript::new(b"IssuanceProof");
        let proof = NIZK::prove(
            &inst,
            witness,
            &inputs,
            &params.spartan_params,
            &mut prover_transcript,
        );

        // Serialize and compress the proof
        #[cfg(feature = "print-trace")]
        {
            let proof_str = bincode::serialize(&proof).unwrap();
            println!("Proof length, serialized by bincode: {} ", proof_str.len());
        }

        let t = start_timer!(|| "Compress proof");
        let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
        bincode::serialize_into(&mut encoder, &proof).unwrap();
        let serialized_snark = encoder.finish().unwrap();
        end_timer!(t);

        #[cfg(feature = "print-trace")]
        {
            let msg_proof_len = format!(
                "SpartanNIZK::proof_compressed_len {:?}",
                serialized_snark.len()
            );
            println!("{}", msg_proof_len);
        }

        Self { serialized_snark }
    }

    pub fn verify(&self, params: &IssuanceProofParams, R0: &NRCurve) -> bool {
        // Decompress and deserialize the proof
        let t = start_timer!(|| "Decompress proof for verification");
        let mut decoder = ZlibDecoder::new(Vec::new());
        if decoder.write_all(&self.serialized_snark).is_err() {
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

        // Build public inputs
        let R0_pt = to_fr_pt(R0);
        let public_inputs = IssuanceCircuitPublicInputs { R0: R0_pt };

        // Spartan verification
        let t = start_timer!(|| "Converting Shape to Instance");
        let inst = match Instance::new_from_shape(&params.shape) {
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
        let mut verifier_transcript = Transcript::new(b"IssuanceProof");
        let result = proof
            .verify(
                &inst,
                &inputs_assign,
                &mut verifier_transcript,
                &params.spartan_params,
            )
            .is_ok();
        end_timer!(t);

        result
    }
}

#[derive(Clone)]
struct IssuanceCircuitPublicInputs {
    R0: Point<Fr>,
}

impl IssuanceCircuitPublicInputs {
    pub fn inputs_vector(&self) -> Vec<Fr> {
        let mut inputs = Vec::new();

        // Always start with 1 to make R1CS solution nontrivial
        inputs.push(Fr::ONE);

        // Add generator point
        let generator = NRCurve::generator();
        inputs.push(fp_to_fr(&generator.x));
        inputs.push(fp_to_fr(&generator.y));
        inputs.push(Fr::ZERO);

        // Add R0 point (x, y, 0) where 0 indicates the point is not at infinity
        inputs.push(self.R0.x);
        inputs.push(self.R0.y);
        inputs.push(Fr::ZERO);

        inputs
    }

    pub fn default() -> Self {
        let generator = to_fr_pt(&NRCurve::generator());
        Self {
            R0: generator.clone(),
        }
    }
}

/// Holds the prover's inputs to the issuance proof circuit
#[derive(Clone)]
struct IssuanceCircuitProverInputs {
    negk0: Fr,
    m: Vec<u8>,
    y: Fr,
}

/// Holds the issuance proof circuit
#[derive(Clone)]
pub struct IssuanceProofCircuit {
    prover_inputs: Option<IssuanceCircuitProverInputs>,
    public_inputs: IssuanceCircuitPublicInputs,
}

impl IssuanceProofCircuit {
    fn new(
        prover_inputs: Option<IssuanceCircuitProverInputs>,
        public_inputs: &IssuanceCircuitPublicInputs,
    ) -> Self {
        Self {
            prover_inputs: prover_inputs.clone(),
            public_inputs: public_inputs.clone(),
        }
    }
}

impl Circuit<Fr> for IssuanceProofCircuit {
    fn synthesize<CS: ConstraintSystem<Fr>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        // Allocate m as bit array
        let mut input_bits = vec![];
        if self.prover_inputs.is_some() {
            let pi = self.prover_inputs.clone().unwrap();
            assert!(pi.m.len() == MSG_LEN_BITS);

            for (byte_i, input_byte) in pi.m.into_iter().enumerate() {
                for bit_i in (0..8).rev() {
                    let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));
                    input_bits.push(
                        AllocatedBit::alloc(cs, Some((input_byte >> bit_i) & 1u8 == 1u8))
                            .unwrap()
                            .into(),
                    );
                }
            }
        } else {
            for (byte_i, _input_byte) in (0..MSG_LEN_BITS).enumerate() {
                for bit_i in (0..8).rev() {
                    let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));
                    input_bits.push(AllocatedBit::alloc(cs, None).unwrap().into());
                }
            }
        }
        // Hash m:
        let Hx_bits = sha256(cs.namespace(|| "SHA256 of m"), &input_bits)?;

        // Convert hash bits to field element (take first 248 bits to fit in Fr)
        // First convert hash output bits from Boolean to AllocatedBit
        let mut allocated_hx_bits = Vec::with_capacity(248);
        for bit in Hx_bits.iter().take(248) {
            // Extract AllocatedBit from Boolean::Is variant
            let allocated_bit = match bit {
                Boolean::Is(allocated) => allocated.clone(),
                _ => unreachable!("Unexpected Boolean variant"),
            };
            allocated_hx_bits.push(allocated_bit);
        }

        // We need to rearrange bits to match the expected endianness for field element conversion
        // First reverse the overall bit order
        allocated_hx_bits.reverse();

        // Then reverse the byte order (keeping bit order within bytes)
        let mut byte_reversed_bits = Vec::with_capacity(allocated_hx_bits.len());
        for byte_idx in (0..(allocated_hx_bits.len() / 8)).rev() {
            let start = byte_idx * 8;
            // Extract each byte's bits and add them in order
            byte_reversed_bits.extend_from_slice(&allocated_hx_bits[start..start + 8]);
        }

        // Convert the arranged bits to a field element (little-endian)
        let Hx = utils::le_bits_to_num(
            cs.namespace(|| "Convert Hx bits to number"),
            &byte_reversed_bits,
        )?;

        // Check (Hx, Hy) is on the curve
        // Allocate Hy from prover's input
        let Hy = match self.prover_inputs.as_ref() {
            Some(inputs) => AllocatedNum::alloc(cs.namespace(|| "allocate Hy"), || Ok(inputs.y))?,
            None => AllocatedNum::alloc(cs.namespace(|| "allocate Hy"), || {
                Err(SynthesisError::AssignmentMissing)
            })?,
        };

        // Create an AllocatedPoint from Hx and Hy
        let is_infinity = AllocatedNum::alloc(cs.namespace(|| "is_infinity"), || Ok(Fr::ZERO))?;
        let H = AllocatedPoint {
            x: Hx,
            y: Hy,
            is_infinity,
        };

        H.assert_on_curve(cs.namespace(|| "H on curve"))?;

        // Allocate generator G
        let generator = NRCurve::generator();
        let G = AllocatedPoint::alloc(
            cs.namespace(|| "G"),
            Some((fp_to_fr(&generator.x), fp_to_fr(&generator.y), false)),
        )?;
        G.inputize(cs.namespace(|| "G input"))?;

        // Allocate k0 from prover's input
        let k0 = match self.prover_inputs.as_ref() {
            Some(inputs) => {
                AllocatedNum::alloc(cs.namespace(|| "allocate k0"), || Ok(inputs.negk0))?
            }
            None => AllocatedNum::alloc(cs.namespace(|| "allocate k0"), || {
                Err(SynthesisError::AssignmentMissing)
            })?,
        };

        // Calculate G^(-k0)
        let Gk0 = G.scalar_mul(cs.namespace(|| "G^k0"), &k0)?;

        // Calculate R0 = H * G^k0
        let calculated_R0 = H.add(cs.namespace(|| "H + G^k0"), &Gk0)?;

        // Allocate public input point R0
        let R0 = AllocatedPoint::alloc(
            cs.namespace(|| "R0"),
            Some((self.public_inputs.R0.x, self.public_inputs.R0.y, false)),
        )?;
        R0.inputize(cs.namespace(|| "R0 input"))?;

        // Constrain the calculated R0 to match the public input R0
        enforce_equal(cs.namespace(|| "check R0.x"), &R0.x, &calculated_R0.x);
        enforce_equal(cs.namespace(|| "check R0.y"), &R0.y, &calculated_R0.y);

        Ok(())
    }
}

impl IssuanceProofCircuit {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nrsig::NRKeyPair;
    use crate::types::convert_F;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use bellpepper_core::Comparable;
    use halo2curves::{group::Curve, CurveAffine};
    use num_format::{Locale, ToFormattedString};
    use rand_core::OsRng;

    #[test]
    pub fn test_issuance_proof_circuit() {
        let m = NRKeyPair::choose_random_message();
        let negk0 = Fq::random(OsRng);
        let Hm = NRKeyPair::hashes_to_curve(&m);
        assert!(Hm.is_some());
        let Hm = Hm.unwrap();
        assert!(bool::from(Hm.is_on_curve()));

        let R0 = (Hm + NRCurve::generator() * (negk0)).to_affine();
        let prover_inputs = IssuanceCircuitProverInputs {
            negk0: convert_F(&negk0),
            m,
            y: convert_F(&Hm.y),
        };

        let public_inputs = IssuanceCircuitPublicInputs { R0: to_fr_pt(&R0) };

        let params = IssuanceProof::create_params();
        let circuit_verifier = IssuanceProofCircuit::new(None, &public_inputs);
        let circuit_prover = IssuanceProofCircuit::new(Some(prover_inputs), &public_inputs);

        let mut cs = TestConstraintSystem::<Fr>::new();
        circuit_prover
            .clone()
            .synthesize(&mut cs.namespace(|| "build_test_vec"))
            .unwrap();

        println!(
            "test_nr_cs: NR circuit has {} constraints and {} aux values",
            cs.num_constraints().to_formatted_string(&Locale::en),
            cs.aux().len().to_formatted_string(&Locale::en)
        );

        assert!(cs.is_satisfied());

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

        let mut prover_transcript = Transcript::new(b"IssuanceProof");
        let t = start_timer!(|| "Generate NIZK proof");
        let proof = NIZK::prove(
            &inst,
            witness,
            &inputs,
            &params.spartan_params,
            &mut prover_transcript,
        );
        end_timer!(t);

        let t = start_timer!(|| "Verify proof");
        let mut verifier_transcript = Transcript::new(b"IssuanceProof");
        assert!(proof
            .verify(
                &inst,
                &inputs,
                &mut verifier_transcript,
                &params.spartan_params
            )
            .is_ok());
        end_timer!(t);

        let proof_str = bincode::serialize(&proof).unwrap();
        println!("Proof length, serialized by bincode: {} ", proof_str.len());

        let t = start_timer!(|| "Compress proof");
        let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
        bincode::serialize_into(&mut encoder, &proof).unwrap();
        let proof_encoded = encoder.finish().unwrap();
        end_timer!(t);

        let msg_proof_len = format!("NIZK::proof_compressed_len {:?}", proof_encoded.len());
        println!("{}", msg_proof_len);
    }
}
