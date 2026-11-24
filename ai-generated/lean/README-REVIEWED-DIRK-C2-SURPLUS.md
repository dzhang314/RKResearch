# Reviewed native DIRK: the full C(2) grade-six surplus

The checked theorem `RKResearch.Certified.Graded.dirk_grade_six_surplus_C2`
proves `dim F3 + 4 <= dim F6` for an actual lower-triangular tableau over
a characteristic-zero field, with reviewed all-tree `HasOrder` of at least 8
and its quadratic stage defect zero (C(2)). In contrast to the earlier
cubic-escape packet, no condition on the F3 clock action is required.
This does not cover non-C(2) tableaux.

* `DIRKC2CoreClock` obtains the exact rank-one physical 0/1 core at one
  clock in the remaining invariant-F3 branch. The shifted Cauchy test
  counts four exterior nonzero clock sites, preserving all physical repetitions.
* `DIRKC2OuterRefund` gives the nonzero heads at the first three exterior
  debuts, and genuinely zero diagonals at the third and fourth. It reuses
  the native Volterra pivot and the earlier origin-cleared Cauchy test.
* `DIRKC2PrefixCompatibility`, `DIRKC2PairedCut` carry one scalar core correction
  plus one shared linear compatibility space on the full physical prefix.
  The paired-rank estimate buys two nonzero inputs with all their specified
  primitive readings zero, without assuming distinct physical rows at any
  repeated clock.
* `DIRKC2BarycentricPort`, `DIRKC2FourDebut` read the barycentric edge and
  three exact primitives from the actual cuts. They reuse the unchanged,
  Mathlib-only `RKCert.FourDebutScalar` proof (source SHA-256
  bc243fd80e176d4ac94a54ca9df0a036dd22b7f20c5dd907382402b2a41f2f54).
  The earlier clock-escaping cubic branch is reused unchanged to close the
  dichotomy. The frozen scalar module was not rebuilt; no sealed numeric
  certificate is imported or replayed.
* `DIRKC2StageJoin` feeds the surplus to the separately verified stage
  budget. The only extra assumption relative to generic lower-triangular
  order is the exact zero quadratic stage defect; the surplus itself is no
  longer a hypothesis. For p>=12 the C(2) uniform bound is
  `p + floor((p-1)/2) - 2 <= s`, giving 15, 17, and 20 stages at orders
  12, 13, and 15 respectively. The stage count also holds over arbitrary
  characteristic-zero commutative rings: the field specialization preserves
  C(2) because this is a zero identity, not a nonzero defect assertion.

Prerequisites: earlier grade-six band/head archive SHA-256
af794b73f29c19d1112add05d2856a0ec4ef28c869e4fd498979302153157aa1,
early cubic closure SHA-256
6010206e0c6b86fbb2d18f3be95e1178d6f96307c64e675b9418bed3486c059c,
and the independent grade-six stage join SHA-256
00e5fa6f575781b0407bf19c5dab996020698513c44ebe82f93ec8992bb0e75c.
All prior and human sources were retained unchanged. The specific reviewed
core is human commit 91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5.

Each of the seven additive source leaves passed pinned Lean 4.36.0
elaboration and independent kernel replay. The audit checks the p=8 field
surplus, p=12 over a ring with torsion, p=13/15 over characteristic-zero
rings, and the declared axiom closures. All checks use cached pinned
Mathlib and previously checked objects. See the source import manifest
for the precise proof closure.
