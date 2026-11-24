# Reviewed DIRK: close the early C(2) cubic-head branch

`RKResearch.Certified.Graded.dirk_grade_six_surplus_of_C2_of_grade_three_escape`
proves `dim F3 + 4 <= dim F6` for an unrestricted lower-triangular tableau over
any characteristic-zero field, with the reviewed `HasOrder p A b`, `8 <= p`,
the actual quadratic defect zero (C(2)), and a genuine clock escape at F3
(`map C F3` is not contained in F3). None of the tableau nodes, weights,
or diagonals are assumed distinct, ordered as field values, or nonzero.

This is one branch of the unconditional grade-six surplus. The F3-invariant
grade-four head and the general non-C(2) case are not closed by this packet.
The existing conditional stage budgets at orders 12, 13, and 15 can consume
the theorem wherever its C(2) and clock-escape hypotheses hold; no unconditional
stage bound or reconstruction of the large arithmetic endpoint is claimed.

* `ClockHeadPaidFlow`: primitive flow on an ordinary clock column plus a genuine
  pure head, and the explicit three-donor / five-dirty-receiver contradiction.
  Spending grade 5→6 allows a quadratic correction to zero three donors, then
  one primitive of degree at most six with a double origin root and four more
  prescribed clock roots; its degree-three head quotient cannot match.
* `ClockSignatureFold`: sum donor taps at each earliest (clock, head) signature.
  Both A applications in the reviewed Volterra operator commute with this
  regrouping on the actual input profile. The regrouped matrix is not assumed
  to have order. No finite stage rows are removed.
* `DIRKCubicCleanTrace`: use the native zero-row Cauchy refund at order eight,
  then the existing matrix Volterra pivot to show the first clean nonzero clock
  is a nonroot with zero physical diagonal and two exact primitive observations.
* `DIRKCubicPivots`, `DIRKCubicCleanDonors`: choose the first five physical
  representative dirty clocks. The first clean row needs four actual dirty
  donor taps. A single derivative test separates that first clean clock from
  any proposed second clean clock before the fifth dirty receiver.
* `DIRKCubicChronology`: use the actual C(2) zero first row to keep the blank
  signature at the origin, then eliminate the fourth dirty and possible
  intervening clean tap at the fifth receiver. This leaves exactly the
  donor support restriction needed by the first leaf's test.

Prerequisites: the sealed grade-six profile packet
SHA-256 af794b73f29c19d1112add05d2856a0ec4ef28c869e4fd498979302153157aa1;
the previously verified native `DIRKOrderSix` (first zero row and anchored
Cauchy test) and `NonsingularDIRKStageFloor` (only Volterra operator, its
tree-to-defect action, and triangular pivot); and their pinned dependencies.
All these inputs are reused unchanged. No legacy tree/order bridge and no
sealed numeric certificate occurs in the import closure.

The six source leaves above were built in dependency order, each independently
kernel-replayed on v4.36.0, and checked by
`AuditReviewedDIRKCubicClosure.lean`. The latter checks the result at its
minimum attained order and prints the eleven axiom closures. See evidence
for the exact direct-import graph, source hashes and replay logs.
