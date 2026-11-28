# Native cardinal quadrature and noncentral marked readout

These four modules continue the characteristic-29 fixed-parameter order-ten
candidate at the same arbitrary local homomorphism to \(\mathbb F_{29}\),
actual decic root \(c\), and actual quadratic roots \(a,b\). They do not assume
a field, a domain or characteristic zero for the coefficient ring.

* `PaidBarycentric.interp` and `PaidBarycentric.low_sum` prove cardinal
  interpolation and the degree-filtered cofactor cancellation over a
  commutative ring, with all pairwise node differences units.
* `Physical.actual_weight_residue`, `actual_weights_unit`, and
  `actual_mu_unit` compute and pay the actual ten cardinal weights and
  seven singleton \(\mu\)-values. The eleventh ordinate is the unscored
  host; its score is zero by definition.
* `Physical.cardinal_exact` proves the ten-node cardinal functional for
  every polynomial of degree at most nine.
  `true_cardinal_numerator` identifies the true singleton numerators
  with the actual cubic/linear \(\mu\), using the quadratic split of the
  actual degree-seven denominator.
* `Physical.weighted_mark_norm` proves the six cofactor marks through
  degree five. `eliminated_marks` proves the three center-eliminated
  weighted \(\boldsymbol\eta\boldsymbol u\) marks, and `completed_u_marks`
  puts them back with the exact pooled center contact through degree three.
  `actual_noncenter_contact` proves the pointwise actual singleton
  \(\boldsymbol w\boldsymbol\eta\) identity, including the unscored host.

The last theorem uses the seven exact nonlinear remainder coefficients and
the actual unit pivot, not a modular spot test. The proofs here do not yet
split the repeated center into two physical rows, derive a strict triangular
weighted decoder, or assert any rooted order for a constructed tableau.

Rebuild from `ai-generated/lean` after the preceding nonlinear modules:
`lake build +RKCert.ReviewedNative.ERK10FixedQ29AdicMarked:olean`.
The source modules print their audited theorem dependencies. The companion
log reports the actual Lean 4.36.0 kernel axioms.
