#![allow(non_snake_case)]

pub mod bellpepper;
mod errors;
mod ipa;
mod ipa_bases;
pub mod ipa_no_zk;
pub mod r1cs;
pub mod transcript;
pub mod utils;

use halo2curves::msm::MsmImplementation;
use halo2curves::CurveAffine;

pub fn msm_function<C: CurveAffine>(scalars: &[C::Scalar], bases: &[C]) -> C::Curve {
    C::specialized_msm(scalars, bases)
}
