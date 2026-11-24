# Unrestricted order-fifteen DIRK: certified supporting structure

The pinned versions are Lean v4.36.0 and Mathlib v4.36.0. The entry point is `RKCert.Dirk15Support`.

**This packet does not prove the 21-stage lower bound, exclude any of the
three remaining cases, or assert existence of a 20-stage method.** It
supplies true-array prerequisites for that exclusion. The existing
unconditional Lean floor at order 15 remains 20. The standalone
mathematical research result and arithmetic replay are not a Lean
certificate.

## True ranks and genuine marking

- `RKCert.Paired.order15_twenty_native_cases`: every hypothetical 20-stage
  lower triangular tableau of actual all-tree order 15 over a
  characteristic-zero field is in one of the following original-array
  cases. No sign or nonvanishing assumptions on individual weights
  enter the case split; nodes may repeat.
  1. Non-C(2): `order15_nonC2_rank_chart` derives the actual last
     weight nonzero, last clock 1, last column zero, actual terminal
     cardinal in `E7`, and `F7` terminal-zero. It gives
     `dim E_j=j+8` over j=7..12, true reverse-orbit identification
     of the full `M_j` over j=2..7, and the case split adds full
     marked clock escape at grades 4..7.
  2. C(2), early full marked surplus: the actual first row is zero,
     `dim M_j=j−1` over j=4..7 and the full marked band escapes at
     each such grade. No terminal-column conclusion is asserted here.
  3. C(2), `dim M4=2`: `order15_minimal_marked_chart` derives the
     actual terminal and last column, `dim M_j^0=j−2` over j=2..7
     and equality with the original paid orbit, terminal-zero
     `F4`, and `Ann(M7^0)=E7+span(e_last)`.
     `order15_minimal_deleted_band` derives
     `bar E_j=Ann(bar M_(14−j)^0)`, rank `j+7`, over j=7..11
     using genuine reflected Hermite escapes. No order of the
     coordinate-deleted array is claimed or used.
- `weighted_reverse_primitive` follows at every paid polynomial
  degree from original tree order, using the bilinear transpose
  and polynomial reflection, never dividing by output weights.
- `nonC2_radau_residual` is the genuine last-cardinal-minus-Radau
  reproducing row in `M7`; `nonC2_radau_port` tests only active
  coordinates already known to annihilate `M7`. There is no
  assertion about dirty coordinates or zero weights.

## Additional inputs to the two-ended argument

- `order15_minimal_cubic_orbit`, `order15_minimal_cubic_sites`,
  and `order15_grade_four_profile` require the explicit first
  grade-three reverse clock escape in the minimal branch. They
  derive the actual five-word polynomial orbit, at least six
  numerical support sites, and the genuine quartic mark
  `tau*v=tau*Q(y)` and active-clean vanishing for `v∈F4`.
  The lower grade-three local possibility is **not** yet excluded here.
- `OrdinaryTrace.two_primitive_first_pivot` and
  `ReverseTrace.two_primitive_last_pivot` get the two necessary
  moments at actual clean chronological pivots of paid traces.
  The forward argument uses no output-weight division. The
  reverse lemma divides only by the pivot's proved nonzero weight
  and pays all discrepancies in the actual terminal-zero flag.
- `Signature.close_mixed_signatures` counts repeated clocks by
  actual multiplicities, only assigning a double root when both
  factors vanish. `affine_factor_from_mixed` supplies exact
  divisibility with repetitions; `affine_gram_zero` derives the
  necessary Gram determinant and `affine_monomial_impossible`
  excludes its monomial base factors. The finite norm nonvanishing,
  earlier chart exclusions, and the full mixed head/chart extraction
  are outside this packet.

The overlay reuses Mathlib's `dotProductEquiv`, dimension of the
dual annihilator, `natDegree_prod_of_monic`, `LinearMap.mulLeft`,
and explicit polynomial reflection/derivative theorems at the
pinned release. `TerminalClean` and `DirkReverseHermite` are the
shared even-DIRK copies; `DirkMarkedBudget` and
`DirkPolynomialMarked` are shared with that track.

## Reproduction

```sh
lake build RKCert.Dirk15Support
lake env lean AuditDIRK15Support.lean
lake env leanchecker --verbose RKCert.Dirk15Support
```

