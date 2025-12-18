#![allow(non_snake_case)]

use criterion::{criterion_group, criterion_main, Criterion};
use r1csipa::ipa_no_zk::InnerProductArg;
use r1csipa::utils::{exp_iter, inner_product};
use halo2curves::ff::Field;
use halo2curves::group::{Curve, Group};
use halo2curves::group::prime::PrimeCurveAffine;
use halo2curves::t256::{Fq as Scalar, T256, T256Affine};
use merlin::Transcript;
use rand_core::OsRng;
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use core::iter;

const BENCHMARK_N: [usize; 4] = [2048, 4096, 8192, 16384];

fn random_bases(n: usize) -> Vec<T256Affine> {
    let bases = (0..n)
        .into_par_iter()
        .map(|_| T256::random(OsRng))
        .collect::<Vec<_>>();
    let mut affine_points = vec![T256Affine::identity(); n];
    T256::batch_normalize(&bases[..], &mut affine_points[..]);
    affine_points
}

fn setup_ipa_test(n: usize) -> (
    Vec<T256Affine>,
    Vec<T256Affine>,
    T256Affine,
    Vec<Scalar>,
    Vec<Scalar>,
    Vec<Scalar>,
    Vec<Scalar>,
    T256Affine,
) {
    let G: Vec<T256Affine> = random_bases(n);
    let H: Vec<T256Affine> = random_bases(n);
    let U = T256Affine::random(OsRng);

    let a: Vec<_> = (0..n).map(|_| Scalar::random(OsRng)).collect();
    let b: Vec<_> = (0..n).map(|_| Scalar::random(OsRng)).collect();
    let c = inner_product(&a, &b);

    let G_factors: Vec<Scalar> = iter::repeat(Scalar::ONE).take(n).collect();
    let y_inv = Scalar::random(OsRng);
    let H_factors: Vec<Scalar> = exp_iter(y_inv).take(n).collect();

    let b_prime = b.iter().zip(exp_iter(y_inv)).map(|(bi, yi)| bi * yi);
    let a_prime = a.iter().cloned();

    use r1csipa::msm_function;
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

    (G, H, U, G_factors, H_factors, a, b, P)
}

fn benchmark_ipa_create(c: &mut Criterion) {
    for &n in &BENCHMARK_N {
        let (G, H, U, G_factors, H_factors, a, b, _P) = setup_ipa_test(n);

        c.bench_function(&format!("IPA {}k create", n / 1024), |bencher| {
            bencher.iter(|| {
                let mut transcript = Transcript::new(b"ipa_benchmark");
                InnerProductArg::create(
                    &mut transcript,
                    &U,
                    &G_factors,
                    &H_factors,
                    G.clone(),
                    H.clone(),
                    a.clone(),
                    b.clone(),
                )
            })
        });
    }
}

fn benchmark_ipa_create_orig_parallel(c: &mut Criterion) {
    for &n in &BENCHMARK_N {
        let (G, H, U, G_factors, H_factors, a, b, _P) = setup_ipa_test(n);

        c.bench_function(&format!("IPA {}k create_orig_parallel", n / 1024), |bencher| {
            bencher.iter(|| {
                let mut transcript = Transcript::new(b"ipa_benchmark");
                InnerProductArg::create_orig_parallel(
                    &mut transcript,
                    &U,
                    &G_factors,
                    &H_factors,
                    G.clone(),
                    H.clone(),
                    a.clone(),
                    b.clone(),
                )
            })
        });
    }
}

fn benchmark_ipa_create_orig(c: &mut Criterion) {
    for &n in &BENCHMARK_N {
        let (G, H, U, G_factors, H_factors, a, b, _P) = setup_ipa_test(n);

        c.bench_function(&format!("IPA {}k create_orig", n / 1024), |bencher| {
            bencher.iter(|| {
                let mut transcript = Transcript::new(b"ipa_benchmark");
                InnerProductArg::create_orig(
                    &mut transcript,
                    &U,
                    &G_factors,
                    &H_factors,
                    G.clone(),
                    H.clone(),
                    a.clone(),
                    b.clone(),
                )
            })
        });
    }
}

fn benchmark_ipa_verify(c: &mut Criterion) {
    for &n in &BENCHMARK_N {
        let (G, H, U, G_factors, H_factors, a, b, P) = setup_ipa_test(n);

        let _y_inv = Scalar::random(OsRng);
        
        // Create a proof using the default create method
        let mut prover_transcript = Transcript::new(b"ipa_benchmark");
        let proof = InnerProductArg::create(
            &mut prover_transcript,
            &U,
            &G_factors,
            &H_factors,
            G.clone(),
            H.clone(),
            a.clone(),
            b.clone(),
        );

        c.bench_function(&format!("IPA {}k verify", n / 1024), |bencher| {
            bencher.iter(|| {
                let mut verifier_transcript = Transcript::new(b"ipa_benchmark");
                proof
                    .verify(
                        &mut verifier_transcript,
                        G_factors.iter(),
                        H_factors.iter(),
                        &P,
                        &U,
                        &G,
                        &H,
                    )
                    .unwrap()
            })
        });
    }
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = benchmark_ipa_create,
    benchmark_ipa_create_orig_parallel,
    benchmark_ipa_create_orig,
    benchmark_ipa_verify
}
criterion_main!(benches);
