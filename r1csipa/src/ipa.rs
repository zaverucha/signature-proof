use crate::errors::ProofError;
use crate::ipa_bases::IPABases;
use crate::msm_function;
use crate::transcript::TranscriptProtocol;
use crate::utils::{batch_invert, inner_product};
use ark_std::{end_timer, start_timer};
use core::iter;
use halo2curves::ff::Field;
use halo2curves::group::Curve;
use halo2curves::serde::endian::EndianRepr;
use halo2curves::serde::SerdeObject;
use halo2curves::CurveAffine;
use halo2curves::CurveExt;
use merlin::Transcript;
use rand_core::OsRng;
use serde::{Deserialize, Serialize};
use std::iter::once;
extern crate alloc;
use alloc::borrow::Borrow;
use alloc::vec::Vec;

// The IPA it compiles down to supports ZK as described by ePrint 2020/735:
// "Bulletproofs+: Shorter Proofs for Privacy-Enhanced Distributed Ledger"
//  Heewon Chung, Kyoohyung Han, Chanyang Ju, Myungsun Kim, and Jae Hong Seo

// The initial IPA code is derived from the dalek Bulletproofs crate/implementation
// https://github.com/zkcrypto/bulletproofs
// of Henry de Valence, Cathie Yun, and Oleg Andreev.
// See inner_product_proof.rs

pub struct IPAParams<C: CurveAffine> {
    pub basesG: Vec<C>, // bases G, H have an equal number of bases
    pub basesH: Vec<C>,
    pub U: C, // Base used for the inner product
    pub V: C, // Base used for the randomness req'd for ZK
}
impl<C: CurveAffine> IPAParams<C> {
    pub fn generate(domain_prefix: &str, n: usize) -> Self {
        // TODO: Parallelize these loops
        let hasher = C::CurveExt::hash_to_curve(domain_prefix);
        // Generate bases by hashing different domain-separated inputs
        let mut basesG = Vec::with_capacity(n);
        for i in 0..n {
            let input = format!("G_{}", i).into_bytes();
            let point = hasher(&input);
            basesG.push(C::from(point));
        }

        let mut basesH = Vec::with_capacity(n);
        for i in 0..n {
            let input = format!("H_{}", i).into_bytes();
            let point = hasher(&input);
            basesH.push(C::from(point));
        }

        let U_point = hasher(b"U_point");
        let U = C::from(U_point);
        let V_point = hasher(b"V_point");
        let V = C::from(V_point);

        Self {
            basesG,
            basesH,
            U,
            V,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InnerProductArgZK<C: CurveAffine> {
    pub(crate) L_vec: Vec<C>,
    pub(crate) R_vec: Vec<C>,
    pub(crate) A: C,
    pub(crate) B: C,
    pub(crate) r: C::Scalar,
    pub(crate) s: C::Scalar,
    pub(crate) delta: C::Scalar,
}

impl<C: CurveAffine + SerdeObject> InnerProductArgZK<C> {
    // Create a ZK proof for IPA instance
    //          P = <a, G> + <b, H> + <a,b>U + alpha*V
    // The value alpha is a random value for hiding, V is an extra parameter.
    // Follows the description of the protocol [...] given in Appendix B of [2025/327], but with notational changes.
    // Overall quite similar to the non-ZK case, but the last iteration is a proof of (a,b) rather than revealing them
    pub fn create(
        transcript: &mut Transcript,
        U: &C,
        V: &C,
        G_factors: &[C::Scalar],
        H_factors: &[C::Scalar],
        mut G_vec: Vec<C>,
        mut H_vec: Vec<C>,
        mut a_vec: Vec<C::Scalar>,
        mut b_vec: Vec<C::Scalar>,
        alpha: C::Scalar,
    ) -> InnerProductArgZK<C>
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
        let mut alpha = alpha;

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

        while n != 1 {
            let t2 = start_timer!(|| format!("iter n = {}", n));
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);

            let (mut G_bases_L, G_bases_R) = G_bases.split_at(n);
            let (mut H_bases_L, H_bases_R) = H_bases.split_at(n);

            let d_L = C::Scalar::random(OsRng);
            let d_R = C::Scalar::random(OsRng);

            let c_L = inner_product(a_L, b_R);
            let c_R = inner_product(a_R, b_L);

            // scalars = [a_L, b_R, c_L, d_L]
            //   bases = [G_R, H_L, U, V]
            let (mut scalars, mut bases) = G_bases_R.get(a_L);
            let (s, bs) = H_bases_L.get(b_R);
            scalars.extend(s);
            bases.extend(bs);
            scalars.push(c_L);
            bases.push(*U);
            scalars.push(d_L);
            bases.push(*V);
            let msm_timer =
                start_timer!(|| format!("Computing L and R with {}-MSMs", scalars.len()));
            let L = msm_function(&scalars, &bases);

            // scalars = [a_R, b_L, c_R, d_R]
            // bases = [G_L, H_R, U, V]
            let (mut scalars, mut bases) = G_bases_L.get(a_R);
            let (s, bs) = H_bases_R.get(b_L);
            scalars.extend(s);
            bases.extend(bs);
            scalars.push(c_R);
            bases.push(*U);
            scalars.push(d_R);
            bases.push(*V);
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
            alpha += u * u * d_L + u_inv * u_inv * d_R;

            a = a_L;
            b = b_L;
            G_bases = G_bases_L;
            H_bases = H_bases_L;

            // if n == 2048 {
            // // TODO: from early tests, collapsing at various points doesn't help.
            //     let s = start_timer!(||format!("Collapsing at n = {}", n));
            //     G_bases.collapse();
            //     H_bases.collapse();
            //     end_timer!(s);
            // }
            end_timer!(t2);
        }

        let n1_timer = start_timer!(|| "Creating proof for n=1 case");
        // Handle the n=1 case
        let r = C::Scalar::random(OsRng);
        let s = C::Scalar::random(OsRng);
        let delta = C::Scalar::random(OsRng);
        let eta = C::Scalar::random(OsRng);

        // Compute A, B as MSMs
        // scalars = [r, s, (r*a + s*b), delta]
        // bases = [G, H, U, V]
        let (mut scalars, mut bases) = G_bases.get(&[r]);
        let (s_H, b_H) = H_bases.get(&[s]);
        scalars.extend(s_H);
        bases.extend(b_H);
        scalars.extend([r * b[0] + s * a[0]]);
        bases.extend([U]);
        scalars.extend([delta]);
        bases.extend([V]);
        let A = msm_function(&scalars, &bases).to_affine();

        // scalars = [r*s, eta]
        // bases = [U, V]
        let B = msm_function::<C>(&[r * s, eta], &[*U, *V]);
        let B = B.to_affine();

        transcript.append_point(b"A", &A);
        transcript.append_point(b"B", &B);
        let e: C::Scalar = transcript.challenge_scalar(b"e");

        let r = r + a[0] * e;
        let s = s + b[0] * e;
        let delta = eta + delta * e + alpha * e * e;
        end_timer!(n1_timer);

        let mut affine_L_vec = vec![C::identity(); L_vec.len()];
        C::Curve::batch_normalize(&L_vec, &mut affine_L_vec);
        let mut affine_R_vec = vec![C::identity(); R_vec.len()];
        C::Curve::batch_normalize(&R_vec, &mut affine_R_vec);
        InnerProductArgZK {
            L_vec: affine_L_vec,
            R_vec: affine_R_vec,
            A,
            B,
            r,
            s,
            delta,
        }
    }

    /// Computes three vectors of verification scalars [u_i^{2}], [u_{i}^{-2}]. Used in verify().
    pub(crate) fn verification_scalars(
        L_vec: &[C],
        R_vec: &[C],
        transcript: &mut Transcript,
    ) -> Result<(Vec<C::Scalar>, Vec<C::Scalar>, Vec<C::Scalar>), ProofError>
    where
        <C as CurveAffine>::ScalarExt: Serialize + EndianRepr,
    {
        let lg_n = L_vec.len();
        let n = 1 << lg_n;

        transcript.append_u64(b"IPA input length n", n as u64);

        // 1. Recompute x_k,...,x_1 based on the proof transcript
        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in L_vec.iter().zip(R_vec.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            let u: C::Scalar = transcript.challenge_scalar(b"u");
            challenges.push(u);
        }

        // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1
        let mut challenges_inv = challenges.clone();
        let allinv = batch_invert(&mut challenges_inv);

        // 3. Compute u_i^2 and (1/u_i)^2
        for i in 0..lg_n {
            // XXX missing square fn upstream
            challenges[i] = challenges[i] * challenges[i];
            challenges_inv[i] = challenges_inv[i] * challenges_inv[i];
        }
        let challenges_sq = challenges;
        let challenges_inv_sq = challenges_inv;

        // 4. Compute s values inductively.
        let mut s = Vec::with_capacity(n);
        s.push(allinv);
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [u_k,...,u_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
            s.push(s[i - k] * u_lg_i_sq);
        }

        Ok((challenges_sq, challenges_inv_sq, s))
    }

    pub fn verify<IG, IH>(
        &self,
        transcript: &mut Transcript,
        G_factors: IG,
        H_factors: IH,
        P: &C,
        U: &C,
        V: &C,
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
        // The single-MSM verification for the ZK case is much like the non-ZK case, in particular the verification_scalars is the same.
        // The equation is given in [2020/735] (with y=1, we don't do weighted inner products)
        // We check:
        //
        //    proof.B ==
        //              <r * e * ver_scalars * G_factors , G> + <s * e * ver_scalars_inv * H_factors, H> +
        //              (rs) U + delta V + (-e^2) P + (-e) A +
        //              <-(e^2)*(u^2), L> + < -(e^2)*(1/u)^2, R>

        let (u_sq, u_inv_sq, ver_scalars_s) =
            Self::verification_scalars(&self.L_vec, &self.R_vec, transcript)?;

        transcript.validate_and_append_point(b"A", &self.A)?;
        transcript.validate_and_append_point(b"B", &self.B)?;
        let e: C::Scalar = transcript.challenge_scalar(b"e");

        let re = self.r * e;
        let g_scalars = G_factors
            .into_iter()
            .zip(ver_scalars_s.iter())
            .map(|(g_i, s_i)| re * s_i * g_i.borrow())
            .take(G.len());

        // 1/s[i] is s[!i], and !i runs from n-1 to 0 as i runs from 0 to n-1
        let ver_scalars_s_inv = ver_scalars_s.iter().rev();
        let se = self.s * e;
        let h_scalars = H_factors
            .into_iter()
            .zip(ver_scalars_s_inv)
            .map(|(h_i, s_i_inv)| se * s_i_inv * h_i.borrow());

        let e_sqr = e * e;
        let l_scalars = u_sq.iter().map(|ui| -*ui * e_sqr);
        let r_scalars = u_inv_sq.iter().map(|ui| -*ui * e_sqr);

        let q_scalar = self.r * self.s;
        let a_scalar = -e;
        let s_scalar = self.delta;
        let p_scalar = -e_sqr;

        let expect_B = msm_function(
            &iter::once(q_scalar)
                .chain(once(a_scalar))
                .chain(once(s_scalar))
                .chain(once(p_scalar))
                .chain(g_scalars)
                .chain(h_scalars)
                .chain(l_scalars)
                .chain(r_scalars)
                .collect::<Vec<C::Scalar>>(),
            &iter::once(U)
                .chain(once(&self.A))
                .chain(once(V))
                .chain(once(P))
                .chain(G.iter())
                .chain(H.iter())
                .chain(self.L_vec.iter())
                .chain(self.R_vec.iter())
                .cloned()
                .collect::<Vec<C>>(),
        );

        if expect_B.to_affine() == self.B {
            Ok(())
        } else {
            println!("expect_B = {:?}", expect_B.to_affine());
            println!("B = {:?}", self.B);
            Err(ProofError::VerificationError)
        }
    }
}

#[cfg(test)]
#[cfg(feature = "pasta")]
mod tests {
    use super::*;
    use rand_core::OsRng;
    use rayon::iter::{IntoParallelIterator, ParallelIterator};
    // use halo2curves::t256::T256 as Projective;
    // use halo2curves::t256::T256Affine as Affine;
    // use halo2curves::t256::Fq as Scalar;
    use halo2curves::group::prime::PrimeCurveAffine;
    use halo2curves::group::Group;
    #[cfg(feature = "pasta")]
    use halo2curves::pasta::Fp as Scalar;
    #[cfg(feature = "pasta")]
    use halo2curves::pasta::Vesta as Projective;
    #[cfg(feature = "pasta")]
    use halo2curves::pasta::VestaAffine as Affine;

    #[test]
    #[cfg(feature = "pasta")]
    fn test_msm() {
        let max_k = 14;

        let bases = (0..1 << max_k)
            .into_par_iter()
            .map(|_| Projective::random(OsRng))
            .collect::<Vec<_>>();
        let mut affine_points = vec![Affine::identity(); 1 << max_k];
        Projective::batch_normalize(&bases[..], &mut affine_points[..]);
        let bases = affine_points;

        let scalars = (0..1 << max_k)
            .into_par_iter()
            .map(|_| Scalar::random(OsRng))
            .collect::<Vec<_>>();

        for k in [11, 12, 13, 14] {
            assert!(k < 64);
            let n: usize = 1 << k;
            let mut acc = Affine::identity().into();
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

    #[cfg(feature = "pasta")]
    fn _random_bases(n: usize) -> Vec<Affine> {
        let bases = (0..n)
            .into_par_iter()
            .map(|_| Projective::random(OsRng))
            .collect::<Vec<_>>();
        let mut affine_points = vec![Affine::identity(); n];
        Projective::batch_normalize(&bases[..], &mut affine_points[..]);
        affine_points
    }

    #[cfg(feature = "pasta")]
    fn test_helper_create_ZK(n: usize) {
        let p: IPAParams<Affine> = IPAParams::generate("ipatestparams", n);

        // a and b are the vectors for which we want to prove c = <a,b>
        let a: Vec<_> = (0..n).map(|_| Scalar::random(OsRng)).collect();
        let b: Vec<_> = (0..n).map(|_| Scalar::random(OsRng)).collect();
        let c = inner_product(&a, &b);

        // alpha is a random value for hiding
        let alpha = Scalar::random(OsRng);

        // No change of bases
        let G_factors: Vec<Scalar> = iter::repeat(Scalar::ONE).take(n).collect();
        let H_factors: Vec<Scalar> = iter::repeat(Scalar::ONE).take(n).collect();

        // Create an instance
        //     P = <a,G> + <b,H> + <a,b> U + alpha V, compute
        let b_prime = b.clone().into_iter();
        let a_prime = a.clone().into_iter();

        let P = msm_function(
            &a_prime
                .chain(b_prime)
                .chain(iter::once(c))
                .chain(iter::once(alpha))
                .collect::<Vec<Scalar>>(),
            &p.basesG
                .iter()
                .chain(p.basesH.iter())
                .chain(iter::once(&p.U))
                .chain(iter::once(&p.V))
                .cloned()
                .collect::<Vec<Affine>>(),
        )
        .to_affine();

        let mut prover_transcript = Transcript::new(b"innerproducttestzk");

        let prover_timer = start_timer!(|| "IPA ZK Prover");

        let proof = InnerProductArgZK::create(
            &mut prover_transcript,
            &p.U,
            &p.V,
            &G_factors,
            &H_factors,
            p.basesG.clone(),
            p.basesH.clone(),
            a.clone(),
            b.clone(),
            alpha,
        );
        end_timer!(prover_timer);

        let bytes = bincode::serialize(&proof).unwrap();
        println!("proof size: {} bytes", bytes.len());

        let ver_time = start_timer!(|| "IPA ZK Verifier");
        let mut verifier = Transcript::new(b"innerproducttestzk");
        assert!(proof
            .verify(
                &mut verifier,
                &G_factors,
                &H_factors,
                &P,
                &p.U,
                &p.V,
                &p.basesG,
                &p.basesH
            )
            .is_ok());
        end_timer!(ver_time);
    }

    #[test]
    fn make_zk_ipa_1() {
        test_helper_create_ZK(1);
    }
    #[test]
    fn make_zk_ipa_2() {
        test_helper_create_ZK(2);
    }
    #[test]
    fn make_zk_ipa_16() {
        test_helper_create_ZK(16);
    }
    #[test]
    fn make_zk_ipa_64() {
        test_helper_create_ZK(64);
    }
    #[test]
    fn make_zk_ipa_1024() {
        test_helper_create_ZK(1024);
    }
    #[test]
    fn make_zk_ipa_2048() {
        test_helper_create_ZK(2048);
    }
    #[test]
    fn make_zk_ipa_4096() {
        test_helper_create_ZK(4096);
    }

    #[test]
    fn make_zk_ipa_8k() {
        test_helper_create_ZK(8192);
    }
    #[test]
    fn make_zk_ipa_16k() {
        test_helper_create_ZK(2 * 8192);
    }
}
