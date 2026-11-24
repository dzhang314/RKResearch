# ERK order-nine one-off midpoint and order-eight shared prefix

Pinned proof check: Lean 4.36.0 (611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9),
Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842, scoped ordinary kernel
leaf builds. The checked proof sources and exact import hashes are included.
No existing project module is changed, no compiled objects are shipped,
and no full or older-toolchain builds are claimed for these new leaves.

Public imports: `RKCert.ERKOrderNineOneOffSixth`,
`RKCert.ERKOrderNineOneOffTerminalShape`. The parent one-off reductions
and amplitude/normal delta are mandatory dependencies on the published
lower-bound hierarchy; use their sealed boundary files, not replacements.

Endpoints in `RKCert.Paired.OneOff` (all over characteristic-zero fields):
* For existing original 12-stage order-nine one-off candidates, `g*h=0`
  on every stage, with no restriction on on/off abscissa overlap.
* `order8_first_four` and `order9_first_four` force the four literal
  numbered features at their existing uniform floors. Equality of features
  is used for a merge only after four grade-two selectors have forced
  equality of all raw incoming row coefficients.
* `order9_fifth_feature`: the fifth row is on at the doubled clock with
  a different cubic defect. `order9_maximal_normal_profile`: genuine
  grade-five rank 10, its exact profile span, nonzero anchored Radau value
  at the doubled clock, and distinction from the terminal.
* `order9_sixth_feature`: the sixth row is clean at a new clock distinct
  from 0, d and 2d, with its exact Ag amplitude. Six prefix rows are
  independent in the genuine grade-four space. Signed interpolation at a
  repeated clock is ruled out without identifying or compressing stages.
* `order9_terminal_normal_profile`: the actual terminal unit has the
  normalized Jacobi endpoint polynomial and its Ag multiplier vanishes
  at the doubled clock. Its nonzero denominator follows from paid moments.

Upstream reuse: Fin.castLE, Fin.ext, Finset.sum_eq_single, LinearMap
rank-nullity and range rank, Submodule.eq_of_le_of_finrank_le,
Polynomial.X_dvd_iff, natDegree_mul and finite-root injectivity. Only the
causal support tests, homogeneous beta moment decoder and native midpoint
gluing are specific to this tableau proof. There is no sign assumption
on the field or on the weights in these leaves.

Still open in this packet: seventh-stage equations and the actual tail
hypotheses that feed the previously checked final scalar tails. No
numerical p8 or p9 promotion is asserted. For p8 this packet proves only
the common one-off prefix; it does not exclude its one- or four-off cases.
