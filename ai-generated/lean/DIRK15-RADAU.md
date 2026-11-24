# Order-fifteen DIRK: audited fixed Radau gates and actual early ranks

This additive overlay targets published main `182d77cc`, keeps the prior
structural and refinement source overlays byte for byte, and leaves the
default imports, toolchain and manifest unchanged. Use
`lake build RKCert.Dirk15RadauSupport` under Lean/Mathlib v4.36.0.

- The physical counts are actual: `order15_nonC2_dirty_count` proves at
  least thirteen reverse cubic-dirty rows and seven occupied cubic sites;
  in the exact nodal cancellation case it uses a true incoming Hermite gain
  on the invariant hull, not a claim that the hull is wholly marked.
  `order15_nonC2_ghost_count` requires two physical simultaneous ghosts.
  `order15_nonC2_clean_port_count` therefore leaves at most five distinct
  truly b-active, cubic-clean ports among the eight fixed Radau sites.
- `order15_nonC2_quartic_channels` and `order15_nonC2_early_ranks` are
  unconditional on the missing-site count or splitting, relative to the
  genuine lower-triangular non-C(2) order-15/s20 hypotheses. They prove
  simultaneous physical quartic disappearance and dim F4=3, dim F5=5.
  The proof finds three missing sites only in the algebraic closure and
  then faithfully descends genuine quartic equations. No RK method is
  reduced at a prime, and no positivity or distinct stage clocks are assumed.
- The two exact fixed arithmetic lifts are
  `left_three_primitive_gram_ne` (245 choices) and
  `right_omitted_primitive_ne` (399 choices). Both are valid in arbitrary
  characteristic-zero fields. The right theorem accepts a product of up
  to four pairwise distinct prescribed right-Radau factors and an omitted
  right-Radau pivot; it does not assert that the unknown DIRK geometry
  produces such a factor. The only modular tests are of the recorded
  fixed prime and fixed roots. Distinctness under the root specialization is
  certified by divided differences and the simple prime factorization.
- `RKCert.Compound.polynomial_factor_exterior_line` gives the exterior
  shift eigenline of an actual monic factor, including repeated or
  nonsplit factors. The generic `gramBlock_det_zero_of_line` is only the
  implication to block determinant zero. There is no computed free-pencil
  norm or norm nonvanishing in this overlay.

This supporting chapter adds no unrestricted stage floor, standalone non-C(2) exclusion or existence claim. The unconditional Lean order-fifteen bound remains 20.
The maximal clock core of rank four, subsequent forward-square geometry,
anchored early/late charts, and nonvanishing of their two-ended norm
remain separate gates.

The later [non-C(2) proof](DIRK15-NONC2-ENDPOINT.md) joins these tests with actual tableau geometry and closes that case.
