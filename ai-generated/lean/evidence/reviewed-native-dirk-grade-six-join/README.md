# Native DIRK grade-six rank-to-stage join

**Scope.** The grade-six surplus itself is not proved here. Over any field, an actual lower triangular tableau of order p ≥ 12 which satisfies

```text
finrank K (zeroSpace A 3) + 4 ≤ finrank K (zeroSpace A 6)
```

has at least **p + ⌊(p−1)/2⌋ − 2 stages**. In particular, the native join gives 15 at order 12, 17 at order 13, 18 at order 14, and 20 at order 15 *assuming that surplus*. If C(2) fails, even order 2m for m≥7 gives 3m−2, including 19 at order 14. This module does not establish the unconditional characteristic-zero endpoints and does not give 21 at order 15.

**Already proved on a concrete class.** The optional `DIRKGradeSixInvariantJoin` adapter imports the independent, checked native band theorem. If any of the forward defect spaces F₄,F₅,F₆ is invariant under multiplication by the physical clock, the stronger floor holds over every characteristic-zero field without a separate surplus premise. Conversely, any shorter tableau over such a field must have all three unit rank gains F₃→F₄→F₅→F₆ and all three noninvariances of F₄,F₅,F₆. The unresolved head exclusions are not assumed or duplicated.

**Unconditional reverse contribution.** `dirk_reverse_room_unanchored` says that `dim(T_q)+n ≤ s` whenever n≥1, q+n+2≤p, and 2q+2≤p, without C(2), any zero first row, characteristic zero, or the grade-six surplus. For p=15 this gives `dim(T₆)+7 ≤ s`. One extra ordinary moment makes a live coordinate at c=1 external to T_q. Subtracting each higher Cauchy row from row zero yields a shifted square kernel whose largest denominator is exactly 2(q+1). If the measured initial backward rank is nonzero, it pays the extra dimension directly. Otherwise D(1) and D(2) both vanish; they force the last live node to one and its closed tail is zero on every backward vector.

**Forward join.** The even and odd marked counts retain any proved surplus beyond unit growth from F₃. For even order, `coeff_defect_tree_rank` counts the separated lower-degree coefficients *inside* the genuine T_m in the non-C(2) branch; a true zero row instead supplies the origin in the C(2) branch. For odd order either the actual nonzero quadratic defect pays, or terminal separation at the true zero row pays. Applying native forward strict growth beyond F₆ propagates its one extra dimension to every later midpoint.

**Field scope.** The rank-to-stage implication uses no `CharZero` hypothesis on a field. Its commutative characteristic-zero ring counterpart `RKResearch.HasOrder.dirk_charZero_count_of_field_grade_six` takes the forward rank input for each characteristic-zero field tableau to which the method can be transported. Rank over the original ring is not treated as a transported field rank, and an arbitrary residue field is not assumed to preserve characteristic zero.

## Entry points

In `RKResearch.Certified.Graded.Reverse`:

- `dirk_reverse_room_of_endpoint`, `dirk_reverse_room_anchored`, `dirk_reverse_room_unanchored`
- `coeff_defect_tree_rank`, `dirk_even_marked_count`, `dirk_odd_marked_count`
- `dirk_uniform_of_grade_six`, `dirk_even_nonC2_of_grade_six`
- `dirk_order_twelve_of_grade_six`, `dirk_order_thirteen_of_grade_six`, `dirk_order_fifteen_of_grade_six`
- Optional: `dirk_uniform_of_invariant_middle_grade`, `dirk_short_forces_grade_six_band`.

## Verification

Only the human tree type, elementary weights Φ and HasOrder from `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5` are used. No alternate order predicate or order bridge enters any proof. The core two new modules depend only on the native uniform floor (prior source delta SHA-256 `75ae905252932c219443d90867bad66899872680f7eb3bbbfa9b069bec759899`), native coefficient specialization and their checked prerequisites. The optional adapter additionally uses the independent grade-six band delta `af794b73f29c19d1112add05d2856a0ec4ef28c869e4fd498979302153157aa1`; its only old-name dependencies are the tree-free Mathlib polynomial lemmas `RKCert.NodalHermiteRank` and `RKCert.NodalPrimitive`. The full transitive source inputs are fingerprinted.

Three warning-free targeted builds, an independent consumer including field/ring scope checks and an invariant-branch use, and three individual kernel replays passed on Lean/Mathlib 4.36.0 (Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). Axiom output contains only `propext`, `Classical.choice`, `Quot.sound`.

With the prerequisites present in the pinned `ai-generated/lean` package:

```sh
lake build RKCert.ReviewedNative.DIRKTerminalRank RKCert.ReviewedNative.DIRKGradeSixJoin RKCert.ReviewedNative.DIRKGradeSixInvariantJoin
lake env lean AuditReviewedNativeDIRKGradeSixJoin.lean
lake env leanchecker --verbose RKCert.ReviewedNative.DIRKTerminalRank
lake env leanchecker --verbose RKCert.ReviewedNative.DIRKGradeSixJoin
lake env leanchecker --verbose RKCert.ReviewedNative.DIRKGradeSixInvariantJoin
```
