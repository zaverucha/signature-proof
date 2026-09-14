#![allow(dead_code)] // Some of the code here is for testing/experimenting
use crate::errors::ProofError;
use crate::ipa_bases::IPABases;
use crate::msm_function;
use crate::transcript::TranscriptProtocol;
use crate::utils::inner_product;
use ark_std::{end_timer, start_timer};
use core::iter;
use halo2curves::ff::Field;
use halo2curves::group::Curve;
use halo2curves::serde::endian::EndianRepr;
use halo2curves::serde::SerdeObject;
use halo2curves::CurveAffine;
use merlin::Transcript;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
extern crate alloc;
use alloc::borrow::Borrow;
use alloc::vec::Vec;
use core::sync::atomic::{AtomicUsize, Ordering};

/// Collapse threshold control for the deferred-MSM prover.
///
/// `0` (the default) selects an *adaptive* threshold derived from the input size; see
/// `InnerProductArg::create` for the mechanism and rationale.  Any non-zero value forces that
/// fixed threshold instead (used for benchmarking the tradeoff); a value larger than the input
/// size disables collapsing entirely.
pub static COLLAPSE_THRESHOLD: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InnerProductArg<C: CurveAffine> {
    pub(crate) L_vec: Vec<C>,
    pub(crate) R_vec: Vec<C>,
    pub(crate) a: C::Scalar,
    pub(crate) b: C::Scalar,
}

impl<C: CurveAffine + SerdeObject> InnerProductArg<C> {
    /// Create an inner-product argument.  (Similar to dalek-bulletproofs, parallelized only in the MSM calls)
    ///
    /// The lengths of the vectors must all be the same, and must all be
    /// either 0 or a power of 2.
    pub fn create_orig(
        transcript: &mut Transcript,
        U: &C,
        G_factors: &[C::Scalar],
        H_factors: &[C::Scalar],
        mut G_vec: Vec<C>,
        mut H_vec: Vec<C>,
        mut a_vec: Vec<C::Scalar>,
        mut b_vec: Vec<C::Scalar>,
    ) -> InnerProductArg<C>
    where
        <C as CurveAffine>::ScalarExt: Serialize + EndianRepr,
    {
        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let mut n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert_eq!(G_factors.len(), n);
        assert_eq!(H_factors.len(), n);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());

        transcript.append_u64(b"IPA input length n", n as u64);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        // If it's the first iteration, unroll the Hprime = H*y_inv scalar mults
        // into multiscalar muls, for performance.
        let t1 = start_timer!(|| "First iter");
        if n != 1 {
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(a_L, b_R);
            let c_R = inner_product(a_R, b_L);

            let L = msm_function(
                &a_L.iter()
                    .zip(G_factors[n..2 * n].iter())
                    .map(|(a_L_i, g)| *a_L_i * g)
                    .chain(
                        b_R.iter()
                            .zip(H_factors[0..n].iter())
                            .map(|(b_R_i, h)| *b_R_i * h),
                    )
                    .chain(iter::once(c_L))
                    .collect::<Vec<C::Scalar>>(),
                &G_R.iter()
                    .chain(H_L.iter())
                    .chain(iter::once(U))
                    .cloned()
                    .collect::<Vec<C>>(),
            );

            let R = msm_function(
                &a_R.iter()
                    .zip(G_factors[0..n].iter())
                    .map(|(a_R_i, g)| *a_R_i * g)
                    .chain(
                        b_L.iter()
                            .zip(H_factors[n..2 * n].iter())
                            .map(|(b_L_i, h)| *b_L_i * h),
                    )
                    .chain(iter::once(c_R))
                    .collect::<Vec<C::Scalar>>(),
                &G_L.iter()
                    .chain(H_R.iter())
                    .chain(iter::once(U))
                    .cloned()
                    .collect::<Vec<C>>(),
            );

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L.to_affine());
            transcript.append_point(b"R", &R.to_affine());

            let u: C::Scalar = transcript.challenge_scalar(b"u");
            let u_inv = u.invert().unwrap();

            let loop_timer = start_timer!(|| "loop to n");
            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = msm_function(
                    &[u_inv * G_factors[i], u * G_factors[n + i]],
                    &[G_L[i], G_R[i]],
                )
                .into();
                H_L[i] = msm_function(
                    &[u * H_factors[i], u_inv * H_factors[n + i]],
                    &[H_L[i], H_R[i]],
                )
                .into();
            }
            end_timer!(loop_timer);

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }
        end_timer!(t1);

        while n != 1 {
            let t2 = start_timer!(|| format!("iter n = {}", n));
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(a_L, b_R);
            let c_R = inner_product(a_R, b_L);

            // scalars = [a_L, b_R, c_L]
            //   bases = [G_R, H_L, U]
            let L = msm_function(
                &a_L.iter()
                    .chain(b_R.iter())
                    .chain(iter::once(&c_L))
                    .cloned()
                    .collect::<Vec<C::Scalar>>(),
                &G_R.iter()
                    .chain(H_L.iter())
                    .chain(iter::once(U))
                    .cloned()
                    .collect::<Vec<C>>(),
            );

            let R = msm_function(
                &a_R.iter()
                    .chain(b_L.iter())
                    .chain(iter::once(&c_R))
                    .cloned()
                    .collect::<Vec<C::Scalar>>(),
                &G_L.iter()
                    .chain(H_R.iter())
                    .chain(iter::once(U))
                    .cloned()
                    .collect::<Vec<C>>(),
            );

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L.to_affine());
            transcript.append_point(b"R", &R.to_affine());

            let u: C::Scalar = transcript.challenge_scalar(b"u");
            let u_inv = u.invert().unwrap();

            let loop_timer = start_timer!(|| "loop to n");
            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];
                G_L[i] = msm_function(&[u_inv, u], &[G_L[i], G_R[i]]).into();
                H_L[i] = msm_function(&[u, u_inv], &[H_L[i], H_R[i]]).into();
            }
            end_timer!(loop_timer);

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
            end_timer!(t2);
        }

        let mut affine_L_vec = vec![C::identity(); L_vec.len()];
        C::Curve::batch_normalize(&L_vec, &mut affine_L_vec);
        let mut affine_R_vec = vec![C::identity(); R_vec.len()];
        C::Curve::batch_normalize(&R_vec, &mut affine_R_vec);
        InnerProductArg {
            L_vec: affine_L_vec,
            R_vec: affine_R_vec,
            a: a[0],
            b: b[0],
        }
    }

    // Create an inner-product argument (similar to dalek-bulletproofs but with MSM and loop parallelization)
    pub fn create_orig_parallel(
        transcript: &mut Transcript,
        U: &C,
        G_factors: &[C::Scalar],
        H_factors: &[C::Scalar],
        mut G_vec: Vec<C>,
        mut H_vec: Vec<C>,
        mut a_vec: Vec<C::Scalar>,
        mut b_vec: Vec<C::Scalar>,
    ) -> InnerProductArg<C>
    where
        <C as CurveAffine>::ScalarExt: Serialize + EndianRepr,
    {
        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let mut n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert_eq!(G_factors.len(), n);
        assert_eq!(H_factors.len(), n);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());

        transcript.append_u64(b"IPA input length n", n as u64);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        // If it's the first iteration, unroll the Hprime = H*y_inv scalar mults
        // into multiscalar muls, for performance.
        let t1 = start_timer!(|| "First iter");
        if n != 1 {
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(a_L, b_R);
            let c_R = inner_product(a_R, b_L);

            let L = msm_function(
                &a_L.iter()
                    .zip(G_factors[n..2 * n].iter())
                    .map(|(a_L_i, g)| *a_L_i * g)
                    .chain(
                        b_R.iter()
                            .zip(H_factors[0..n].iter())
                            .map(|(b_R_i, h)| *b_R_i * h),
                    )
                    .chain(iter::once(c_L))
                    .collect::<Vec<C::Scalar>>(),
                &G_R.iter()
                    .chain(H_L.iter())
                    .chain(iter::once(U))
                    .cloned()
                    .collect::<Vec<C>>(),
            );

            let R = msm_function(
                &a_R.iter()
                    .zip(G_factors[0..n].iter())
                    .map(|(a_R_i, g)| *a_R_i * g)
                    .chain(
                        b_L.iter()
                            .zip(H_factors[n..2 * n].iter())
                            .map(|(b_L_i, h)| *b_L_i * h),
                    )
                    .chain(iter::once(c_R))
                    .collect::<Vec<C::Scalar>>(),
                &G_L.iter()
                    .chain(H_R.iter())
                    .chain(iter::once(U))
                    .cloned()
                    .collect::<Vec<C>>(),
            );

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L.to_affine());
            transcript.append_point(b"R", &R.to_affine());

            let u: C::Scalar = transcript.challenge_scalar(b"u");
            let u_inv = u.invert().unwrap();

            let loop_timer = start_timer!(|| "loop to n");
            // Calculate all new values in parallel
            let new_values: Vec<_> = (0..n)
                .into_par_iter()
                .map(|i| {
                    let new_a_L_i = a_L[i] * u + u_inv * a_R[i];
                    let new_b_L_i = b_L[i] * u_inv + u * b_R[i];

                    let new_G_L_i = msm_function::<C>(
                        &[u_inv * G_factors[i], u * G_factors[n + i]],
                        &[G_L[i], G_R[i]],
                    )
                    .into();

                    let new_H_L_i = msm_function(
                        &[u * H_factors[i], u_inv * H_factors[n + i]],
                        &[H_L[i], H_R[i]],
                    )
                    .into();

                    (i, new_a_L_i, new_b_L_i, new_G_L_i, new_H_L_i)
                })
                .collect();

            // Update the original arrays with the new values
            for (i, new_a, new_b, new_g, new_h) in new_values {
                a_L[i] = new_a;
                b_L[i] = new_b;
                G_L[i] = new_g;
                H_L[i] = new_h;
            }
            end_timer!(loop_timer);

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }
        end_timer!(t1);

        while n != 1 {
            let t2 = start_timer!(|| format!("iter n = {}", n));
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(a_L, b_R);
            let c_R = inner_product(a_R, b_L);

            // scalars = [a_L, b_R, c_L]
            //   bases = [G_R, H_L, U]
            let L = msm_function(
                &a_L.iter()
                    .chain(b_R.iter())
                    .chain(iter::once(&c_L))
                    .cloned()
                    .collect::<Vec<C::Scalar>>(),
                &G_R.iter()
                    .chain(H_L.iter())
                    .chain(iter::once(U))
                    .cloned()
                    .collect::<Vec<C>>(),
            );

            let R = msm_function(
                &a_R.iter()
                    .chain(b_L.iter())
                    .chain(iter::once(&c_R))
                    .cloned()
                    .collect::<Vec<C::Scalar>>(),
                &G_L.iter()
                    .chain(H_R.iter())
                    .chain(iter::once(U))
                    .cloned()
                    .collect::<Vec<C>>(),
            );

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L.to_affine());
            transcript.append_point(b"R", &R.to_affine());

            let u: C::Scalar = transcript.challenge_scalar(b"u");
            let u_inv = u.invert().unwrap();

            let loop_timer = start_timer!(|| "loop to n");
            // Calculate all new values in parallel
            let new_values: Vec<_> = (0..n)
                .into_par_iter()
                .map(|i| {
                    let new_a_L_i = a_L[i] * u + u_inv * a_R[i];
                    let new_b_L_i = b_L[i] * u_inv + u * b_R[i];
                    let new_G_L_i = msm_function(&[u_inv, u], &[G_L[i], G_R[i]]).into();
                    let new_H_L_i = msm_function(&[u, u_inv], &[H_L[i], H_R[i]]).into();

                    (i, new_a_L_i, new_b_L_i, new_G_L_i, new_H_L_i)
                })
                .collect();

            // Update the original arrays with the new values
            for (i, new_a, new_b, new_g, new_h) in new_values {
                a_L[i] = new_a;
                b_L[i] = new_b;
                G_L[i] = new_g;
                H_L[i] = new_h;
            }
            end_timer!(loop_timer);

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
            end_timer!(t2);
        }

        let mut affine_L_vec = vec![C::identity(); L_vec.len()];
        C::Curve::batch_normalize(&L_vec, &mut affine_L_vec);
        let mut affine_R_vec = vec![C::identity(); R_vec.len()];
        C::Curve::batch_normalize(&R_vec, &mut affine_R_vec);
        InnerProductArg {
            L_vec: affine_L_vec,
            R_vec: affine_R_vec,
            a: a[0],
            b: b[0],
        }
    }

    // Version using the defer strategy where all scalar mults are done as MSMs and loops are parallelized
    pub fn create(
        transcript: &mut Transcript,
        U: &C,
        G_factors: &[C::Scalar],
        H_factors: &[C::Scalar],
        mut G_vec: Vec<C>,
        mut H_vec: Vec<C>,
        mut a_vec: Vec<C::Scalar>,
        mut b_vec: Vec<C::Scalar>,
    ) -> InnerProductArg<C>
    where
        <C as CurveAffine>::ScalarExt: Serialize + EndianRepr,
    {
        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let G = &mut G_vec[..];
        let H = &mut H_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let mut n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert_eq!(G_factors.len(), n);
        assert_eq!(H_factors.len(), n);

        // All of the input vectors must have a length that is a power of two.
        assert!(n.is_power_of_two());

        transcript.append_u64(b"IPA input length n", n as u64);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        let mut G_bases = IPABases::new(n);
        let mut H_bases = IPABases::new(n);

        for i in 0..n {
            G_bases.defer_init(&[G_factors[i]], &[G[i]]);
            H_bases.defer_init(&[H_factors[i]], &[H[i]]);
        }

        // Number of deferred terms currently carried by each symbolic base.  It doubles every
        // round (via `defer`) and is reset to 1 whenever we collapse.
        let mut terms_per_base = 1usize;
        // Resolve the collapse threshold.  The default (0) picks an adaptive value: collapse once
        // each symbolic base reaches ~`n/256` terms, clamped to [8, 32].  This keeps the first
        // collapse's materialized MSMs in the efficient small-MSM regime (<= 32 elements, where
        // halo2curves stays on the serial path and avoids nested-rayon oversubscription) while
        // still amortizing the expensive full-size head rounds.  A non-zero atomic value forces a
        // fixed threshold (for benchmarking; a value > n disables collapsing).
        let collapse_threshold = match COLLAPSE_THRESHOLD.load(Ordering::Relaxed) {
            0 => (n / 256).clamp(8, 32),
            forced => forced,
        };

        while n != 1 {
            let t2 = start_timer!(|| format!("iter n = {}", n));
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);

            let (mut G_bases_L, G_bases_R) = G_bases.split_at(n);
            let (mut H_bases_L, H_bases_R) = H_bases.split_at(n);

            let c_L = inner_product(a_L, b_R);
            let c_R = inner_product(a_R, b_L);

            // scalars = [a_L, b_R, c_L]
            //   bases = [G_R, H_L, U]
            let (mut scalars, mut bases) = G_bases_R.get(a_L);
            let (s, bs) = H_bases_L.get(b_R);
            scalars.extend(s);
            bases.extend(bs);
            scalars.push(c_L);
            bases.push(*U);
            let msm_timer =
                start_timer!(|| format!("Computing L and R with {}-MSMs", scalars.len()));
            let L = msm_function(&scalars, &bases);

            // scalars = [a_R, b_L, c_R]
            // bases = [G_L, H_R, U]
            let (mut scalars, mut bases) = G_bases_L.get(a_R);
            let (s, bs) = H_bases_R.get(b_L);
            scalars.extend(s);
            bases.extend(bs);
            scalars.push(c_R);
            bases.push(*U);
            let R = msm_function(&scalars, &bases);

            end_timer!(msm_timer);

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L.to_affine());
            transcript.append_point(b"R", &R.to_affine());

            let u: C::Scalar = transcript.challenge_scalar(b"u");
            let u_inv = u.invert().unwrap();

            let loop_timer = start_timer!(|| "loop to n");
            for i in 0..n {
                a_L[i] = a_L[i] * u + u_inv * a_R[i];
                b_L[i] = b_L[i] * u_inv + u * b_R[i];

                G_bases_L.defer(i, &G_bases_R, &[u_inv, u]);
                H_bases_L.defer(i, &H_bases_R, &[u, u_inv]);
            }
            end_timer!(loop_timer);

            a = a_L;
            b = b_L;
            G_bases = G_bases_L;
            H_bases = H_bases_L;

            // Each `defer` above doubled the terms-per-base; collapse once it reaches the
            // threshold so that subsequent L/R MSMs shrink with the vector length.
            terms_per_base *= 2;
            if terms_per_base >= collapse_threshold && n != 1 {
                let collapse_timer = start_timer!(|| format!("Collapse at n = {}", n));
                G_bases.collapse();
                H_bases.collapse();
                terms_per_base = 1;
                end_timer!(collapse_timer);
            }
            end_timer!(t2);
        }

        let mut affine_L_vec = vec![C::identity(); L_vec.len()];
        C::Curve::batch_normalize(&L_vec, &mut affine_L_vec);
        let mut affine_R_vec = vec![C::identity(); R_vec.len()];
        C::Curve::batch_normalize(&R_vec, &mut affine_R_vec);
        InnerProductArg {
            L_vec: affine_L_vec,
            R_vec: affine_R_vec,
            a: a[0],
            b: b[0],
        }
    }

    // This verify methods works for proofs created with any of the above methods.
    pub fn verify<IG, IH>(
        &self,
        transcript: &mut Transcript,
        G_factors: IG,
        H_factors: IH,
        P: &C,
        U: &C,
        G: &[C],
        H: &[C],
    ) -> Result<(), ProofError>
    where
        IG: IntoIterator,
        IG::Item: Borrow<C::Scalar>,
        IH: IntoIterator,
        IH::Item: Borrow<C::Scalar>,
        <C as CurveAffine>::ScalarExt: Serialize + EndianRepr,
    {
        let (u_sq, u_inv_sq, s) = crate::ipa::InnerProductArgZK::verification_scalars(
            &self.L_vec,
            &self.R_vec,
            transcript,
        )?;

        let g_times_a_times_s = G_factors
            .into_iter()
            .zip(s.iter())
            .map(|(g_i, s_i)| (self.a * s_i) * g_i.borrow())
            .take(G.len());

        // 1/s[i] is s[!i], and !i runs from n-1 to 0 as i runs from 0 to n-1
        let inv_s = s.iter().rev();

        let h_times_b_div_s = H_factors
            .into_iter()
            .zip(inv_s)
            .map(|(h_i, s_i_inv)| (self.b * s_i_inv) * h_i.borrow());

        let neg_u_sq = u_sq.iter().map(|ui| -*ui);
        let neg_u_inv_sq = u_inv_sq.iter().map(|ui| -*ui);

        let expect_P = msm_function(
            &iter::once(self.a * self.b)
                .chain(g_times_a_times_s)
                .chain(h_times_b_div_s)
                .chain(neg_u_sq)
                .chain(neg_u_inv_sq)
                .collect::<Vec<C::Scalar>>(),
            &iter::once(U)
                .chain(G.iter())
                .chain(H.iter())
                .chain(self.L_vec.iter())
                .chain(self.R_vec.iter())
                .cloned()
                .collect::<Vec<C>>(),
        );

        if expect_P.to_affine() == *P {
            Ok(())
        } else {
            println!("expect_P = {:?}", expect_P.to_affine());
            println!("*P = {:?}", *P);
            Err(ProofError::VerificationError)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::exp_iter;
    use halo2curves::group::prime::PrimeCurveAffine;
    use halo2curves::group::Group;
    use halo2curves::t256::Fq as Scalar;
    use halo2curves::t256::T256Affine;
    use halo2curves::t256::T256;
    use rand_core::OsRng;
    use rayon::iter::{IntoParallelIterator, ParallelIterator};

    #[test]
    fn try_msm() {
        let max_k = 14;

        let bases = (0..1 << max_k)
            .into_par_iter()
            .map(|_| T256::random(OsRng))
            .collect::<Vec<_>>();
        let mut affine_points = vec![T256Affine::identity(); 1 << max_k];
        T256::batch_normalize(&bases[..], &mut affine_points[..]);
        let bases = affine_points;

        let scalars = (0..1 << max_k)
            .into_par_iter()
            .map(|_| Scalar::random(OsRng))
            .collect::<Vec<_>>();

        for k in [11, 12, 13, 14] {
            assert!(k < 64);
            let n: usize = 1 << k;
            let mut acc = T256Affine::identity().into();
            halo2curves::msm::msm_serial(&scalars[..n], &bases[..n], &mut acc);
            let res1 = halo2curves::msm::msm_parallel(&scalars[..n], &bases[..n]);
            let t = start_timer!(|| format!("msm timer k = {}", k));
            //let res2 = halo2curves::msm::msm_best(&scalars[..n], &bases[..n]);
            let res2 = msm_function(&scalars[..n], &bases[..n]);
            end_timer!(t);

            assert!(res1 == res2);
            assert!(res2 == acc);
        }
    }

    fn random_bases(n: usize) -> Vec<T256Affine> {
        let bases = (0..n)
            .into_par_iter()
            .map(|_| T256::random(OsRng))
            .collect::<Vec<_>>();
        let mut affine_points = vec![T256Affine::identity(); n];
        T256::batch_normalize(&bases[..], &mut affine_points[..]);
        affine_points
    }

    fn test_helper_create<F>(n: usize, create_fn: F)
    where
        F: Fn(
            &mut Transcript,
            &T256Affine,
            &[Scalar],
            &[Scalar],
            Vec<T256Affine>,
            Vec<T256Affine>,
            Vec<Scalar>,
            Vec<Scalar>,
        ) -> InnerProductArg<T256Affine>,
    {
        //use crate::generators::BulletproofGens;   // TODO: use param generation in R1CS, so that someone can use the IPA code indep.
        //let bp_gens = BulletproofGens::new(n, 1);
        let G: Vec<T256Affine> = random_bases(n); // bp_gens.share(0).G(n).cloned().collect();
        let H: Vec<T256Affine> = random_bases(n); //bp_gens.share(0).H(n).cloned().collect();
                                                  // U is parameter used for the inner product
        let U = T256Affine::random(OsRng);

        // a and b are the vectors for which we want to prove c = <a,b>
        let a: Vec<_> = (0..n).map(|_| Scalar::random(OsRng)).collect();
        let b: Vec<_> = (0..n).map(|_| Scalar::random(OsRng)).collect();
        let c = inner_product(&a, &b);

        let G_factors: Vec<Scalar> = iter::repeat(Scalar::ONE).take(n).collect();

        // y_inv is (the inverse of) a random challenge
        let y_inv = Scalar::random(OsRng);
        let H_factors: Vec<Scalar> = exp_iter(y_inv).take(n).collect();

        // P would be determined upstream, but we need a correct P to check the proof.
        //
        // To generate P = <a,G> + <b,H'> + <a,b> U, compute
        //             P = <a,G> + <b',H> + <a,b> U,
        // where b' = b \circ y^(-n)
        let b_prime = b.iter().zip(exp_iter(y_inv)).map(|(bi, yi)| bi * yi);
        let a_prime = a.iter().cloned();

        let P = msm_function(
            &a_prime
                .chain(b_prime)
                .chain(iter::once(c))
                .collect::<Vec<Scalar>>(),
            &G.iter()
                .chain(H.iter())
                .chain(iter::once(&U))
                .cloned()
                .collect::<Vec<T256Affine>>(),
        )
        .to_affine();

        let mut prover_transcript = Transcript::new(b"innerproducttest");

        let prover_timer = start_timer!(|| "IPA Prover");

        let proof = create_fn(
            &mut prover_transcript,
            &U,
            &G_factors,
            &H_factors,
            G.clone(),
            H.clone(),
            a.clone(),
            b.clone(),
        );
        end_timer!(prover_timer);

        let bytes = bincode::serialize(&proof).unwrap();
        println!("proof size: {} bytes", bytes.len());

        let ver_time = start_timer!(|| "IPA Verifier");
        let mut verifier = Transcript::new(b"innerproducttest");
        assert!(proof
            .verify(
                &mut verifier,
                iter::repeat(Scalar::ONE).take(n),
                exp_iter(y_inv).take(n),
                &P,
                &U,
                &G,
                &H
            )
            .is_ok());
        end_timer!(ver_time);
    }

    #[test]
    fn make_ipa_1() {
        test_helper_create(1, &InnerProductArg::create);
    }

    #[test]
    fn make_ipa_2() {
        test_helper_create(2, &InnerProductArg::create);
    }

    #[test]
    fn make_ipa_128() {
        test_helper_create(128, &InnerProductArg::create);
    }
    #[test]
    fn make_ipa_8k() {
        test_helper_create(8192, &InnerProductArg::create);
    }

    // Run with: cargo test --release -p r1csipa sweep_collapse_threshold -- --ignored --nocapture
    #[test]
    #[ignore]
    fn sweep_collapse_threshold() {
        use std::time::Instant;
        for &n in &[2048usize, 4096, 8192, 16384] {
            let G: Vec<T256Affine> = random_bases(n);
            let H: Vec<T256Affine> = random_bases(n);
            let U = T256Affine::random(OsRng);
            let a: Vec<_> = (0..n).map(|_| Scalar::random(OsRng)).collect();
            let b: Vec<_> = (0..n).map(|_| Scalar::random(OsRng)).collect();
            let G_factors: Vec<Scalar> = iter::repeat(Scalar::ONE).take(n).collect();
            let y_inv = Scalar::random(OsRng);
            let H_factors: Vec<Scalar> = exp_iter(y_inv).take(n).collect();

            println!("==== n = {} ====", n);
            for &t in &[usize::MAX, 4, 8, 16, 32, 64, 128, 256, 512] {
                COLLAPSE_THRESHOLD.store(t, Ordering::Relaxed);
                let run = || {
                    InnerProductArg::create(
                        &mut Transcript::new(b"bench"),
                        &U,
                        &G_factors,
                        &H_factors,
                        G.clone(),
                        H.clone(),
                        a.clone(),
                        b.clone(),
                    )
                };
                let _ = run(); // warmup
                let reps = 8;
                let start = Instant::now();
                for _ in 0..reps {
                    let _ = run();
                }
                let elapsed = start.elapsed() / reps;
                let label = if t == usize::MAX {
                    "none".to_string()
                } else {
                    t.to_string()
                };
                println!(
                    "  threshold {:>5}: {:>8.3} ms",
                    label,
                    elapsed.as_secs_f64() * 1e3
                );
            }
        }
    }

    #[test]
    fn make_ipa_8k_original_parallel() {
        test_helper_create(8192, &InnerProductArg::create_orig_parallel);
    }

    #[test]
    fn make_ipa_8k_original() {
        test_helper_create(8192, &InnerProductArg::create_orig);
    }

    // Compare the halo2curves MSM dispatch choices at the exact sizes our prover uses.
    // The production dispatcher routes len with `ceil(ln(len)) < 10` (i.e. len < ~8103) to
    // `msm_parallel`; this sweep checks whether the scheduled affine-batch path (forced via an
    // explicit window size `c`) would be faster for those medium sizes.
    // Run with: cargo test --release -p r1csipa sweep_msm_dispatch -- --ignored --nocapture
    #[test]
    #[ignore]
    fn sweep_msm_dispatch() {
        use halo2curves::msm::{msm_parallel, msm_scheduled_with_c, msm_serial_with_c};
        use std::time::Instant;

        // +1 mirrors the extra `U` term in each L/R MSM.
        let sizes = [33usize, 257, 1025, 4097, 8193, 16385, 32769, 65537, 131073];

        for &len in &sizes {
            let bases = random_bases(len);
            let scalars: Vec<Scalar> = (0..len).map(|_| Scalar::random(OsRng)).collect();

            let reference = msm_parallel(&scalars, &bases);

            let reps: u32 = if len < 1024 {
                300
            } else if len < 4096 {
                40
            } else if len < 20000 {
                12
            } else {
                4
            };
            let bench = |f: &dyn Fn() -> T256| -> f64 {
                let _ = f(); // warmup
                let start = Instant::now();
                for _ in 0..reps {
                    let _ = f();
                }
                start.elapsed().as_secs_f64() * 1e3 / reps as f64
            };

            let t_par = bench(&|| msm_parallel(&scalars, &bases));
            print!("len {:>6}: parallel {:>8.3} |", len, t_par);

            // Scheduled path across candidate window sizes.
            for c in 8..=16usize {
                assert_eq!(
                    msm_scheduled_with_c(&scalars, &bases, c),
                    reference,
                    "scheduled c={} wrong at len={}",
                    c,
                    len
                );
                let t = bench(&|| msm_scheduled_with_c(&scalars, &bases, c));
                print!(" {}={:>6.3}", c, t);
            }

            // For the small collapse size, also sweep the serial window size.
            if len < 64 {
                for c in 3..=6usize {
                    let t = bench(&|| {
                        let mut acc = T256::identity().into();
                        msm_serial_with_c(&scalars, &bases, &mut acc, c);
                        acc
                    });
                    print!(" ser{}={:>6.3}", c, t);
                }
            }
            println!();
        }
    }
}
