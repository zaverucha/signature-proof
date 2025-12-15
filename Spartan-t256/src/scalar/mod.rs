use ff::Field;

pub type Scalar = crate::group::ScalarField;

pub trait ScalarFromPrimitives {
    fn to_scalar(self) -> Scalar;
}

impl ScalarFromPrimitives for usize {
    #[inline]
    fn to_scalar(self) -> Scalar {
        (0..self).map(|_i| Scalar::one()).sum()
    }
}

impl ScalarFromPrimitives for bool {
    #[inline]
    fn to_scalar(self) -> Scalar {
        if self {
            Scalar::one()
        } else {
            Scalar::zero()
        }
    }
}

pub fn batch_invert(inputs: &mut [Scalar]) -> Scalar {
    // This code is essentially identical to the FieldElement
    // implementation, and is documented there.  Unfortunately,
    // it's not easy to write it generically, since here we want
    // to use `UnpackedScalar`s internally, and `Scalar`s
    // externally, but there's no corresponding distinction for
    // field elements.
    // We also remove the zeroization support since halo2curves
    // does not support it

    let n = inputs.len();
    let one = Scalar::one();

    let scratch_vec = vec![one; n];
    let mut scratch = scratch_vec;

    // Keep an accumulator of all of the previous products
    let mut acc = Scalar::one();

    // Pass through the input vector, recording the previous
    // products in the scratch space
    for (input, scratch) in inputs.iter().zip(scratch.iter_mut()) {
        *scratch = acc;

        acc = acc * input;
    }

    // acc is nonzero iff all inputs are nonzero
    debug_assert!(acc != Scalar::zero());

    // Compute the inverse of all products
    acc = acc.invert().unwrap();

    // We need to return the product of all inverses later
    let ret = acc;

    // Pass through the vector backwards to compute the inverses
    // in place
    for (input, scratch) in inputs.iter_mut().rev().zip(scratch.iter().rev()) {
        let tmp = &acc * input.clone();
        *input = &acc * scratch;
        acc = tmp;
    }

    ret
}
