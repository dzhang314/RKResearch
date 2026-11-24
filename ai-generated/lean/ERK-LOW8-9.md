# Explicit Runge–Kutta low-order charts: orders eight and nine

This source release adds checked **necessary conditions**, not a proof that
the limiting candidates do not exist. In particular it must not be cited as
an end-to-end certificate of order eight requiring 11 stages or order nine
requiring 13 stages. The established numerical floor in the inherited ring
theorems remains 10 and 12 respectively.

## Import and exact scope

Import `RKCert.ERKLowFourOff` for the low-order dependency closure, or
`RKCert` for the entire package. The major results use a literal
`RKCert.StrictLower A` and `RKCert.HasTreeOrderAtLeast A b p` with the original
stage vector and output weights, not abstract assumed rank conditions. They
are stated over arbitrary characteristic-zero fields, so also apply over
ordered fields. No positivity, distinctness of physical rows, support of a
specific pattern, or an assumed simplified order condition is used.

* `RKCert.Paired.order8_ten_stage_chart`: the final output weight is nonzero;
  D(1) holds; the actual final abscissa is 1; the last coordinate column belongs
  to E4 but not E3. The defect ranks F3/F4 are 2/3, and full tree ranks E3/E4
  are 6/8. E5 has rank at most 9; the two quadratic reverse directions span
  the E4 annihilator.
* `RKCert.Paired.order8_treeSpace_four_not_clock_invariant`: E4 is not
  invariant under multiplication by the actual abscissae.
* `RKCert.Paired.order8_off_count_chart`: if the ten-stage chart existed,
  the number N of distinct off nodes would be 1, 4, 5, or at least 7.
  `order8_five_on_of_middle_offs` forces exactly five distinct on nodes for
  N=4 or N=5.
* `RKCert.Paired.order9_twelve_stage_chart`: the final output weight is
  nonzero; the same midpoint ranks apply, E5 has rank 9 or 10, and E6 has
  rank at most 11. `order9_rank_five_full` establishes the terminal
  coordinate, D(1), and the backward rank obstruction when E5 has rank 10.
* `RKCert.Paired.order9_treeSpace_five_not_clock_invariant`: E5 is
  not invariant under multiplication by the actual abscissae, at either
  of its possible ranks. The reflected degree-four primitive tests are
  actual all-tree order consequences. In the rank-ten case the reverse
  Hermite target is the terminal-zero cross section of the E4 annihilator.
* `RKCert.Paired.order9_reduced_off_count_chart`: if the twelve-stage
  chart existed, N would be one or at least five. This includes the complete
  N=2, N=3, and N=4 branches of the order-nine two-curve proof. N=4 uses
  state interpolation, both E5 ranks, and the terminal-zero proof above.
  No on-stage state at node 1 is possible when precisely five on nodes
  carry the order-nine moments; the proof is a four-row rational identity,
  not positivity or real-root interlacing.

## Reusable lemmas

`ERKLowBase` gives exact truncation for a zero-weight *suffix* (not an
internal row), exact tree/defect splitting where the moment budget permits,
and the nilpotence bound for restrictions. `ERKMergeRows` is a separate
certificate for merging two *literally identical* incoming rows. Same
state only implies agreement on the specified state function space; it
does not license a merge.

`ERKLowCurves`, `ERKLowMoments`, and `ERKLowThreeOff` give genuine
two-curve extraction, probe-based cancellation of off-feature aggregates,
an anchored shifted Cauchy moment test, and the first-on-node chronology
for the three-off case. In these statements an off feature is distinct
from an on feature at the same abscissa: the state is an abscissa tagged
by which curve it belongs to. `ERKLowStates` gives its exact dimension and
separate interpolation on the two finite node sets. All rank claims refer
to actual full-coordinate spaces.

`ERKLowReverseHermite` independently checks the small Hermite restriction
for three (1−X)^2-weighted polynomial rows. The primary chart
non-invariance proof instead consumes the common reverse-gain toolkit,
and uses `clock_not_of_anchored_adjacent_gap` for both the order-eight
case and the saturated part of order nine.

## Remaining proofs

* Order eight: the original source is J. C. Butcher, *The non-existence of
  ten stage eighth order explicit Runge–Kutta methods*, BIT 25 (1985),
  521–540, DOI 10.1007/BF01935372. Only the publication/abstract was
  available for this pass, not the original argument. The ten-stage chart
  above leaves N=1, N=4, N=5 and N≥7 open. The partial lemmas do not imply 11.
* Order nine: the supplied `Runge_Kutta_Shorter_Proofs_and_Stronger_Bounds`
  manuscript, sections 2–6, gives the rank/non-invariance and two-curve
  structures implemented here. The remaining N=1, N=5, N=6, N=7 and
  N≥8 branches still need formal extraction and gates. In particular,
  the documented modular elimination (`pass0345_rk9` and its companion
  endpoint passes) is not silently assumed as a lemma. The partial
  lemmas do not imply 13.

## Mathlib reuse

Pinned Lean + Mathlib 4.36.0 only. The common grade-five sources are
byte-identical to the inherited release. The four shared forward Hermite
modules are also byte-identical to the verified logarithmic toolkit,
and the three reverse toolkit modules are copied byte-identically from
the order-twelve reverse workspace. No new custom axiom, native oracle,
or skipped proof is used.

Native APIs used include `IsNilpotent.charpoly_eq_X_pow_finrank`,
`LinearMap.aeval_self_charpoly`, `mul_apply_eq_comp` for endomorphism action, `Subspace.finrank_add_finrank_dualAnnihilator_eq`,
`LinearMap.finrank_range_of_inj`, `Module.finrank_fintype_fun_eq_card`,
`Submodule.eq_of_le_of_finrank_le`, `Lagrange.interpolate`,
`Lagrange.eval_interpolate_at_node`,
`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`,
`Finset.card_filter_add_card_filter_not`, `Fin.sum_univ_succAbove`, and
`Fin.succAboveOrderEmb`. The nilpotence-at-an-earlier-coordinate lemma
carries an explicit chronological coordinate estimate, unlike a global
nilpotence theorem. The rank and polynomial arithmetic use Mathlib;
chronological row restriction, actual tree pairing, and the endpoint
moment budget are RK-specific.

