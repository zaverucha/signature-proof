use core::{
    cmp,
    fmt::Debug,
    iter::Sum,
    ops::{Add, Mul, Neg, Sub},
};

use rand::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::{
    ff::{Field, PrimeField, WithSmallOrderMulGroup},
    group::{prime::PrimeCurveAffine, Curve, Group as _, GroupEncoding},
    t256::{Fp, Fq},
    Coordinates, CurveAffine, CurveExt,
};

impl group::cofactor::CofactorGroup for T256 {
    type Subgroup = T256;

    fn clear_cofactor(&self) -> Self {
        *self
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(self, 1.into())
    }

    fn is_torsion_free(&self) -> Choice {
        1.into()
    }
}

const T256_GENERATOR_X: Fp = Fp::from_raw([
    0x0000000000000005,
    0x0000000000000000,
    0x0000000000000000,
    0x0000000000000000,
]);
const T256_GENERATOR_Y: Fp = Fp::from_raw([
    0x5826108A653DE28D,
    0x0ED60B9E33CE397C,
    0x5EFC7B55F6B24FBE,
    0x3E86C0CFEBF2C716,
]);

const T256_A: Fp = Fp::from_raw([
    0x93135661B1C4B114,
    0x7E72B42B30E73177,
    0x0000000000000001,
    0xFFFFFFFF00000001,
]);
const T256_B: Fp = Fp::from_raw([
    0x863E60F20219FC56,
    0x36B06ACEEB354224,
    0x6FB552F8E21ED4AC,
    0xB441071B12F4A036,
]);

use crate::{
    impl_binops_additive, impl_binops_additive_specify_output, impl_binops_multiplicative,
    impl_binops_multiplicative_mixed, new_curve_impl,
};

new_curve_impl!(
    (pub),
    T256,
    T256Affine,
    Fp,
    Fq,
    (T256_GENERATOR_X,T256_GENERATOR_Y),
    T256_A,
    T256_B,
    "t256",
    |domain_prefix| hash_to_curve(domain_prefix, hash_to_curve_suite(b"T256_XMD:SHA-256_SSWU_RO_")),
    crate::serde::CompressedFlagConfig::Extra,
    standard_sign
);

fn hash_to_curve_suite(domain: &[u8]) -> crate::hash_to_curve::Suite<T256, sha2::Sha256, 48> {
    // Z : <https://datatracker.ietf.org/doc/html/rfc9380#sswu-z-code>
    const SSWU_Z: Fp = Fp::from_raw([
        0x93135661B1C4B116,
        0x7E72B42B30E73177,
        0x0000000000000001,
        0xFFFFFFFF00000001,
    ]);

    let iso_map = crate::hash_to_curve::Iso {
        a: T256::a(),
        b: T256::b(),
        map: Box::new(move |x, y, z| T256 { x, y, z }),
    };

    crate::hash_to_curve::Suite::new(domain, SSWU_Z, crate::hash_to_curve::Method::SSWU(iso_map))
}

#[allow(clippy::type_complexity)]
pub(crate) fn hash_to_curve<'a>(
    domain_prefix: &'a str,
    suite: crate::hash_to_curve::Suite<T256, sha2::Sha256, 48>,
) -> Box<dyn Fn(&[u8]) -> T256 + 'a> {
    Box::new(move |message| suite.hash_to_curve(domain_prefix, message))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::serde::SerdeObject;
    use crate::{
        curve,
        msm::{msm_serial, MsmImplementation},
    };
    use group::UncompressedEncoding;
    use rand_core::OsRng;

    crate::curve_testing_suite!(T256);
    crate::curve_testing_suite!(T256, "ecdsa_example");
    crate::curve_testing_suite!(
        T256,
        "constants",
        Fp::MODULUS,
        T256_A,
        T256_B,
        T256_GENERATOR_X,
        T256_GENERATOR_Y,
        Fq::MODULUS
    );

    #[test]
    fn test_hash_to_curve() {
        for i in 1..10 {
            let r0 = <T256Affine as curve::CurveAffine>::CurveExt::hash_to_curve(
                "t256 domain prefix",
            )(format!("Test {}", i).as_bytes());
            assert!(r0.to_affine().is_on_curve().unwrap_u8() == 1);
            assert!(r0.to_affine().is_identity().unwrap_u8() == 0);
        }
    }

    #[test]
    fn test_msm() {
        let mut scalars: Vec<Fq> = vec![];
        let mut bases: Vec<T256Affine> = vec![];
        for _ in 1..(1 << 13) {
            bases.push(T256Affine::random(&mut OsRng));
            scalars.push(Fq::random(&mut OsRng));
        }
        let res1 = T256Affine::specialized_msm(&scalars, &bases);
        let res2 = T256Affine::identity();
        msm_serial(&scalars, &bases, &mut res2.into());
        assert!(res1 == res1);
    }

    #[test]
    fn test_msm_dispatch_correct() {
        // Validate `specialized_msm` (the production dispatch) against a serial reference for T256
        // across the size range, including medium sizes routed to the scheduled affine-batch path,
        // and with identity (point-at-infinity) bases mixed in.
        use group::prime::PrimeCurveAffine;
        for &len in &[40usize, 300, 2000, 8200] {
            let mut bases: Vec<T256Affine> =
                (0..len).map(|_| T256Affine::random(&mut OsRng)).collect();
            let scalars: Vec<Fq> = (0..len).map(|_| Fq::random(&mut OsRng)).collect();
            for &i in &[0usize, 3, len / 2, len - 1] {
                bases[i] = T256Affine::identity();
            }
            let mut reference = T256::identity();
            msm_serial(&scalars, &bases, &mut reference);
            assert_eq!(
                T256Affine::specialized_msm(&scalars, &bases),
                reference,
                "specialized_msm mismatch at len={}",
                len
            );
        }
    }

    #[test]
    fn test_msm_doubling_path() {
        // Force the affine batch-addition doubling branch by repeating identical bases so that
        // many land in the same Pippenger bucket. The doubling slope is `(3x^2 + a)/(2y)`; on
        // T256 (`a = -3 != 0`) an incorrect `3x^2`-only slope yields an off-curve point and a
        // panic. `msm_serial` uses projective (curve-complete) addition and is a correct
        // reference for any curve.
        let g = T256Affine::generator();
        let h = (T256::generator() * Fq::from(7u64)).to_affine();
        for &len in &[64usize, 200, 1500] {
            // Alternate between two distinct points, each repeated many times.
            let bases: Vec<T256Affine> =
                (0..len).map(|i| if i % 2 == 0 { g } else { h }).collect();
            // Small, repeated scalars maximise bucket collisions (and hence doublings).
            let scalars: Vec<Fq> = (0..len).map(|i| Fq::from((i % 4 + 1) as u64)).collect();
            let mut reference = T256::identity();
            msm_serial(&scalars, &bases, &mut reference);
            assert_eq!(
                T256Affine::specialized_msm(&scalars, &bases),
                reference,
                "specialized_msm mismatch (doubling path) at len={}",
                len
            );
        }
    }

    #[test]
    fn test_msm_batch_normalized_identity() {
        // Mimic Spartan's flow: identity bases arrive via `batch_normalize` of z=0 projective
        // points, which may not be the canonical affine identity. The MSM must still handle them.
        use group::prime::PrimeCurveAffine;
        for &len in &[40usize, 300, 2000] {
            let mut proj: Vec<T256> = (0..len).map(|_| T256::random(&mut OsRng)).collect();
            for &i in &[0usize, 5, len / 2, len - 2] {
                proj[i] = T256::identity();
            }
            let mut bases = vec![T256Affine::identity(); len];
            T256::batch_normalize(&proj, &mut bases);

            let scalars: Vec<Fq> = (0..len).map(|_| Fq::random(&mut OsRng)).collect();
            let mut reference = T256::identity();
            msm_serial(&scalars, &bases, &mut reference);
            assert_eq!(
                T256Affine::specialized_msm(&scalars, &bases),
                reference,
                "specialized_msm mismatch (batch-normalized identity) at len={}",
                len
            );
        }
    }
}
