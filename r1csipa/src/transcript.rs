//! Defines a `TranscriptProtocol` trait for using a Merlin transcript.
use core::panic;

use halo2curves::ff::PrimeField;
use halo2curves::serde::endian::EndianRepr;
use halo2curves::serde::SerdeObject;
use halo2curves::CurveAffine;
use merlin::Transcript;

use crate::errors::ProofError;

pub trait TranscriptProtocol {
    /// Append a domain separator for an `n`-bit, `m`-party range proof.
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64);

    /// Append a domain separator for a length-`n` inner product proof.
    fn innerproduct_domain_sep(&mut self, n: u64);

    /// Append a domain separator for a constraint system.
    fn r1cs_domain_sep(&mut self);

    /// Commit a domain separator for a CS without randomized constraints.
    fn r1cs_1phase_domain_sep(&mut self);

    /// Commit a domain separator for a CS with randomized constraints.
    fn r1cs_2phase_domain_sep(&mut self);

    /// Append a `scalar` with the given `label`.
    fn append_scalar<F: PrimeField + EndianRepr>(&mut self, label: &'static [u8], scalar: &F);

    /// Append a `point` with the given `label`.
    fn append_point<C: CurveAffine + SerdeObject>(&mut self, label: &'static [u8], point: &C);

    /// Check that a point is not the identity, then append it to the
    /// transcript.  Otherwise, return an error.
    fn validate_and_append_point<C: CurveAffine + SerdeObject>(
        &mut self,
        label: &'static [u8],
        point: &C,
    ) -> Result<(), ProofError>;

    /// Compute a `label`ed challenge variable.
    fn challenge_scalar<F: PrimeField + EndianRepr>(&mut self, label: &'static [u8]) -> F;
}

impl TranscriptProtocol for Transcript {
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64) {
        self.append_message(b"dom-sep", b"rangeproof v1");
        self.append_u64(b"n", n);
        self.append_u64(b"m", m);
    }

    fn innerproduct_domain_sep(&mut self, n: u64) {
        self.append_message(b"dom-sep", b"ipp v1");
        self.append_u64(b"n", n);
    }

    fn r1cs_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs v1");
    }

    fn r1cs_1phase_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs-1phase");
    }

    fn r1cs_2phase_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs-2phase");
    }

    fn append_scalar<F: PrimeField + EndianRepr>(&mut self, label: &'static [u8], scalar: &F) {
        self.append_message(label, &scalar.to_bytes());
    }

    fn append_point<C: CurveAffine + SerdeObject>(&mut self, label: &'static [u8], point: &C) {
        self.append_message(label, &point.to_raw_bytes());
    }

    fn validate_and_append_point<C: CurveAffine + SerdeObject>(
        &mut self,
        label: &'static [u8],
        point: &C,
    ) -> Result<(), ProofError> {
        if bool::from(point.is_identity()) {
            Err(ProofError::VerificationError)
        } else {
            self.append_message(label, &point.to_raw_bytes());
            Ok(())
        }
    }

    fn challenge_scalar<F: PrimeField + EndianRepr>(&mut self, label: &'static [u8]) -> F {
        let mut u_bytes: [u8; 32] = [0; 32];
        self.challenge_bytes(label, &mut u_bytes);
        if F::CAPACITY < 256 && F::CAPACITY >= 248 {
            u_bytes[31] = 0;
        } else if F::CAPACITY == 256 {
            // Do nothing
        } else {
            panic!("Field is smaller than expected");
        }
        F::from_bytes(&u_bytes).unwrap()
    }
}
