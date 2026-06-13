use halo2curves::ff::Field;
use halo2curves::group::Curve;
use halo2curves::CurveAffine;
use rayon::prelude::*;

// Represent each base symbolically, as (bases, scalars), such that base = msm(bases, scalars)
// When we later use the base in an MSM, say as base^x, we compute (bases, x*scalars) and
// add this list of terms (bases[1]^scalars[1], ..., ) as terms in the MSM
#[derive(Clone)]
pub struct IPABases<C: CurveAffine, F: Field> {
    bases: Vec<Vec<C>>,
    scalars: Vec<Vec<F>>,
}

impl<C: CurveAffine<ScalarExt = F>, F: Field> IPABases<C, F> {
    pub fn new(n: usize) -> Self {
        let bases = Vec::with_capacity(n);
        let scalars = Vec::with_capacity(n);
        IPABases { bases, scalars }
    }

    pub fn defer_init(&mut self, scalars: &[F], bases: &[C]) {
        assert!(
            scalars.len() == bases.len(),
            "Scalars and bases must have same length"
        );
        self.scalars.push(scalars.to_vec());
        self.bases.push(bases.to_vec());
    }

    // self is the left half
    // Update G_L[i] to  G_L[i] * scalars[0], (just update the scalars, don't actually compute the scalar mult)
    // then append G_R[i] * scalars[1], (again not the scalar mult)
    pub fn defer(&mut self, i: usize, bases_R: &Self, scalars: &[F]) {
        assert!(scalars.len() == 2);

        for k in 0..self.scalars[i].len() {
            self.scalars[i][k] *= scalars[0];
        }

        for k in 0..bases_R.bases[i].len() {
            self.scalars[i].push(bases_R.scalars[i][k] * scalars[1]);
            self.bases[i].push(bases_R.bases[i][k]);
        }
    }

    /// Split the bases at the given index, returning two separate IPABases
    /// structures representing the left and right halves.
    ///
    /// Consumes `self` and moves the underlying per-base term vectors into the two
    /// halves, avoiding any per-base cloning of the (potentially large) symbolic
    /// representation.
    pub fn split_at(mut self, n: usize) -> (Self, Self) {
        assert!(n <= self.bases.len(), "Split index out of bounds");

        let right_bases = self.bases.split_off(n);
        let right_scalars = self.scalars.split_off(n);

        let left = IPABases {
            bases: self.bases,
            scalars: self.scalars,
        };
        let right = IPABases {
            bases: right_bases,
            scalars: right_scalars,
        };

        (left, right)
    }

    /// Get the scalars and bases associated with the given values
    ///
    /// This method takes a slice of scalars and returns a tuple containing:
    /// 1. A vector of scalars (combining the input scalars with the internal scalars)
    /// 2. A vector of bases (corresponding bases for the scalars)
    pub fn get(&self, values: &[F]) -> (Vec<F>, Vec<C>) {
        assert!(
            values.len() == self.bases.len(),
            "Input length must match bases length"
        );

        let mut result_scalars = Vec::with_capacity(values.len());
        let mut result_bases = Vec::with_capacity(values.len());

        for (i, value) in values.iter().enumerate() {
            // For each scalar in the input, we multiply it with all stored scalars
            // for the corresponding base and add to the result
            for j in 0..self.scalars[i].len() {
                result_scalars.push(*value * self.scalars[i][j]);
                result_bases.push(self.bases[i][j]);
            }
        }

        (result_scalars, result_bases)
    }

    // collapse: replaces each symbolic base by the single point msm(scalars[i], bases[i]) and
    // resets its scalar to ONE.  This caps the number of deferred terms per base (and hence the
    // size of subsequent L/R MSMs) at the cost of one batch of small MSMs.
    pub fn collapse(&mut self) {
        use halo2curves::group::Group;
        // Materialize every symbolic base via its MSM, parallelizing ACROSS bases.
        // Each per-base MSM is computed serially (msm_serial) to avoid nested rayon
        // parallelism: collapsing runs a par_iter over bases, and if each inner MSM also
        // spawned threads it would oversubscribe the pool and dominate the runtime.
        let projective: Vec<C::Curve> = (0..self.bases.len())
            .into_par_iter()
            .map(|i| {
                let mut acc = C::Curve::identity();
                halo2curves::msm::msm_serial(&self.scalars[i], &self.bases[i], &mut acc);
                acc
            })
            .collect();

        // Convert all results to affine using a single batched field inversion.
        let mut affine = vec![C::identity(); projective.len()];
        C::Curve::batch_normalize(&projective, &mut affine);

        for (i, point) in affine.into_iter().enumerate() {
            self.bases[i] = vec![point];
            self.scalars[i] = vec![F::ONE];
        }
    }
}
