use crate::r1cs::{R1CSMatrix, R1CSProof, R1CSProofParams};
use ark_std::{end_timer, start_timer};
use halo2curves::ff::{Field, PrimeField};
use serde::Deserialize;
use subtle::ConstantTimeEq;
extern crate alloc;
use crate::r1cs::R1CSInstance;
use alloc::vec::Vec;
use halo2curves::serde::endian::EndianRepr;
use halo2curves::serde::SerdeObject;
use halo2curves::CurveAffine;
use merlin::Transcript;
use serde::Serialize;

pub struct Powers<F: PrimeField> {
    x: F,
    next_exp_x: F,
}

impl<F: PrimeField> Iterator for Powers<F> {
    type Item = F;

    fn next(&mut self) -> Option<F> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter<F: PrimeField>(x: F) -> Powers<F> {
    let next_exp_x = F::ONE;
    Powers { x, next_exp_x }
}

//from https://github.com/zkcrypto/ff/blob/41fb01b8990909b8b1b44d4601556694c473bc16/src/batch.rs
pub fn batch_invert<F>(scalars: &mut Vec<F>) -> F
where
    F: Field + ConstantTimeEq,
{
    let mut acc = F::ONE;
    //let iter = self.into_iter();
    let mut tmp = alloc::vec::Vec::with_capacity(scalars.len());
    for p in scalars {
        let q = *p;
        tmp.push((acc, p));
        acc = F::conditional_select(&(acc * q), &acc, q.is_zero());
    }
    acc = acc.invert().unwrap();
    let allinv = acc;

    for (tmp, p) in tmp.into_iter().rev() {
        let skip = p.is_zero();

        let tmp = tmp * acc;
        acc = F::conditional_select(&(acc * *p), &acc, skip);
        *p = F::conditional_select(&tmp, p, skip);
    }

    allinv
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
pub fn inner_product<F: PrimeField>(a: &[F], b: &[F]) -> F {
    let mut out = F::ZERO;
    if a.len() != b.len() {
        panic!("inner_product(a,b): lengths of vectors do not match");
    }
    for i in 0..a.len() {
        out += a[i] * b[i];
    }
    out
}

pub fn multiply_vec<F: PrimeField>(
    num_rows: usize,
    num_cols: usize,
    M: &R1CSMatrix<F>,
    z: &[F],
) -> Vec<F> {
    assert_eq!(
        z.len(),
        num_cols,
        "multiply_vec: vector length not equal to number of columns"
    );

    // Initialize the result vector with zeros
    let mut result = vec![F::ZERO; num_rows];

    // For each non-zero element in the matrix
    for (row, col, val) in M.iter() {
        // Multiply the matrix element at (row,col) by the vector element at 'col'
        // and add to the result at position 'row'
        result[*row] += *val * z[*col];
    }

    result
}

/// Multiplies a vector by a sparse matrix
///
/// Performs vector-matrix multiplication where the input vector has length equal to
/// the number of rows in the matrix, and the output vector has length equal to the
/// number of columns in the matrix.
pub fn vec_multiply_mat<F: PrimeField>(
    num_rows: usize,
    num_cols: usize,
    M: &R1CSMatrix<F>,
    v: &[F],
) -> Vec<F> {
    assert_eq!(
        v.len(),
        num_rows,
        "vec_multiply_mat: vector length not equal to number of rows"
    );

    // Initialize the result vector with zeros
    let mut result = vec![F::ZERO; num_cols];

    // For each non-zero element in the matrix
    for (row, col, val) in M.iter() {
        // Multiply the vector element at 'row' by the matrix element at (row,col)
        // and add to the result at position 'col'
        result[*col] += v[*row] * *val;
    }

    result
}

/// Computes the component-wise (Hadamard) product of two vectors
///
/// Returns a vector where each element is the product of the corresponding elements in a and b
pub fn component_wise_mul<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    assert_eq!(
        a.len(),
        b.len(),
        "Vectors must have the same length for component-wise multiplication"
    );

    a.iter()
        .zip(b.iter())
        .map(|(a_i, b_i)| *a_i * *b_i)
        .collect()
}

/// Compares two vectors for equality
///
/// Returns true if the vectors are equal, false otherwise
pub fn vec_compare<F: PrimeField>(a: Vec<F>, b: Vec<F>) -> bool {
    if a.len() != b.len() {
        return false;
    }

    for (a_i, b_i) in a.iter().zip(b.iter()) {
        if a_i != b_i {
            return false;
        }
    }

    true
}

/// Adds two vectors element-wise
///
/// Returns a vector where each element is the sum of the corresponding elements in a and b
pub fn add_vec<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    assert_eq!(
        a.len(),
        b.len(),
        "Vectors must have the same length for element-wise addition"
    );

    a.iter()
        .zip(b.iter())
        .map(|(a_i, b_i)| *a_i + *b_i)
        .collect()
}

/// Multiplies each element of a vector by a scalar
///
/// Returns a new vector where each element is the result of multiplying
/// the corresponding element in the input vector by the scalar
pub fn vector_scalar_mul<F: PrimeField>(v: &[F], scalar: &F) -> Vec<F> {
    v.iter().map(|element| *element * scalar).collect()
}

/// Subtracts the second vector from the first element-wise
///
/// Returns a vector where each element is the result of subtracting the corresponding
/// element in b from the corresponding element in a
pub fn sub_vec<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    assert_eq!(
        a.len(),
        b.len(),
        "Vectors must have the same length for element-wise subtraction"
    );

    a.iter()
        .zip(b.iter())
        .map(|(a_i, b_i)| *a_i - *b_i)
        .collect()
}

pub fn check_r1cs_instance<F: PrimeField>(
    rows: usize,
    cols: usize,
    A: &R1CSMatrix<F>,
    B: &R1CSMatrix<F>,
    C: &R1CSMatrix<F>,
    z: &[F],
) -> bool {
    let a = multiply_vec(rows, cols, A, z);
    let b = multiply_vec(rows, cols, B, z);
    let c = multiply_vec(rows, cols, C, z);
    let ab = component_wise_mul(&a, &b);
    vec_compare(ab, c)
}

pub fn test_helper_r1cs_proof<C: CurveAffine + SerdeObject + Serialize + for<'b> Deserialize<'b>>(
    r: &R1CSInstance<C::Scalar>,
    witness: &Vec<C::Scalar>,
) where
    <C as CurveAffine>::ScalarExt: Serialize + for<'a> Deserialize<'a> + EndianRepr,
{
    let params = R1CSProofParams::<C>::generate("params for r1cs proof test", r.rows + r.cols);

    let mut prover_transcript = Transcript::new(b"r1csprooftest");
    let s = start_timer!(|| "R1CS prover");
    let proof = R1CSProof::create(r, witness, &params, &mut prover_transcript);
    end_timer!(s);

    let s = start_timer!(|| "R1CS verifier");
    let mut verifier_transcript = Transcript::new(b"r1csprooftest");
    let result = R1CSProof::verify(r, &params, &mut verifier_transcript, &proof).is_ok();
    end_timer!(s);

    assert!(result, "R1CS proof failed to verify");

    let bytes = bincode::serialize(&proof).unwrap();
    println!("proof size: {} bytes", bytes.len());
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::msm_function;
    #[allow(unused_imports)]
    use ark_std::{end_timer, start_timer};
    use halo2curves::group::prime::PrimeCurveAffine;
    use halo2curves::group::{Curve, Group};
    #[allow(unused_imports)]
    use halo2curves::t256::Fq as Scalar;
    use halo2curves::t256::{T256Affine, T256};
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
            let res2 = msm_function(&scalars[..n], &bases[..n]);
            end_timer!(t);

            assert!(res1 == res2);
            assert!(res2 == acc);
        }
    }

    #[allow(dead_code)]
    fn random_bases(n: usize) -> Vec<T256Affine> {
        let bases = (0..n)
            .into_par_iter()
            .map(|_| T256::random(OsRng))
            .collect::<Vec<_>>();
        let mut affine_points = vec![T256Affine::identity(); n];
        T256::batch_normalize(&bases[..], &mut affine_points[..]);
        affine_points
    }

    #[test]
    fn test_inner_product() {
        let a = vec![
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
        ];
        let b = vec![
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(5u64),
        ];
        assert_eq!(Scalar::from(40u64), inner_product(&a, &b));
    }
}
