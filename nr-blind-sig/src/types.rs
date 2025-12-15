#![allow(non_snake_case)]

use ff::PrimeField;
use num_bigint::BigInt;
use num_traits::Num;

// In this file we define types for the elliptic curve and field parameters used in the library
// They are compile-time choices, make a change here to change the curve

use halo2curves::{serde::endian::EndianRepr, CurveAffine};

use crate::emulated::field_element::EmulatedFieldParams;

// Using secp256r1 (P-256) as the Signing curve (NR), t256 as the proving curve (Pi)

// Using secq256k1 as the Signing curve, secp256k1 as the proving curve
// pub type NRCurve = halo2curves::secq256k1::Secq256k1Affine;
// pub type PiCurve = halo2curves::secp256k1::Secp256k1Affine;
// pub const CURVE_A : i32 = 0;

#[cfg(feature = "vesta")]
mod curve_impl {
    // Using pallas as the Signing curve, vesta as the proving curve
    pub type NRCurve = halo2curves::pasta::PallasAffine;
    pub type PiCurve = halo2curves::pasta::VestaAffine;
    pub const CURVE_A: i32 = 0;
}
#[cfg(all(feature = "t256", not(feature = "vesta")))]
mod curve_impl {
    // Using P-256 as the signing curve, T-256 as the proving curve
    pub type NRCurve = halo2curves::secp256r1::Secp256r1Affine;
    pub type PiCurve = halo2curves::t256::T256Affine;
    pub const CURVE_A: i32 = -3;
}
// Re-export everything from the selected curve_impl module
pub use curve_impl::*;

/// The base field of the curve used for NR signatures.
/// The field that the proof system uses for arithmetic circuits
/// (the scalar field in the proof system).
/// Mathematically these are the same field, but they are different Rust types
pub type Fp = <NRCurve as CurveAffine>::Base;
pub type Fr = <PiCurve as CurveAffine>::ScalarExt;

/// The scalar field of the curve used for NR signatures
pub type Fq = <NRCurve as CurveAffine>::ScalarExt;

pub fn fp_to_fr(a: &Fp) -> Fr {
    Fr::from_bytes(&a.to_bytes()).unwrap()
}

pub fn fq_to_fr(a: &Fq) -> Fr {
    Fr::from_bytes(&a.to_bytes()).unwrap()
}

pub fn fr_to_fq(a: &Fr) -> Fq {
    Fq::from_bytes(&a.to_bytes()).unwrap()
}

pub fn convert_F<F1: PrimeField + EndianRepr, F2: PrimeField + EndianRepr>(a: &F1) -> F2 {
    F2::from_bytes(&a.to_bytes()).unwrap()
}

#[allow(non_snake_case)]
pub fn digest_to_F<F: PrimeField + EndianRepr>(digest: &[u8; 32]) -> F {
    if F::CAPACITY == 256 {
        F::from_bytes(digest).unwrap()
    } else if F::CAPACITY < 256 && F::CAPACITY >= 248 {
        let mut digest = *digest;
        digest[31] = 0;
        F::from_bytes(&digest).unwrap()
    } else {
        panic!("Field is smaller than expected");
    }
}

pub struct FqEmulatedParams;
impl EmulatedFieldParams for FqEmulatedParams {
    fn num_limbs() -> usize {
        16
    }

    fn bits_per_limb() -> usize {
        16
    }

    fn modulus() -> BigInt {
        let modulus = Fq::MODULUS;
        // Remove "0x" prefix if present
        let clean_modulus = modulus.strip_prefix("0x").unwrap_or(modulus);
        BigInt::from_str_radix(clean_modulus, 16).unwrap()
    }

    fn is_modulus_pseudo_mersenne() -> bool {
        false
    }

    fn pseudo_mersenne_params() -> Option<crate::emulated::field_element::PseudoMersennePrime> {
        None
    }
}
