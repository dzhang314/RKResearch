# Native ordered ERK9: only the physical (5,6) chart remains

The checked theorem `RKResearch.Certified.Graded.MultiOff.order9_no_five_off_five_on`
excludes five defective and five clean knots on the original twelve-stage
matrix over **every characteristic-zero field**. Combined with the earlier
two additive native census packets, an arbitrary ordered twelve-stage ERK9
candidate must have **exactly five defective and six clean clocks**.
`explicit_order_nine_outside_five_six_at_least_thirteen` gives the stage floor
(13\le s) without any assumptions other than strict explicitness, reviewed
order, and being outside that sole residual chart.

The first adjoint row is derived from the reviewed reflected primitive
budget. Clean and defective weights at a shared clock remain separate.
The Radau branch uses the paid four- and fifth-grade states, a literal
one-dimensional duplicate-state contrast, and its incoming row difference.
Surjectivity into all ten cohorts fixes the chronological locations without
replacing the internal tableau by a quotient. The final scalar gate only
uses previously checked polynomial and scalar declarations; no residue
arithmetic was replayed.

The physical six-clean chart, its K8 compatibility, and its terminal
product remain a separate step. No unconditional stage floor is claimed in
this packet.

Validation: Lean 4.36.0 / mathlib 4.36.0 on unchanged reviewed human basis
`91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. Requires the prior additive
multi-low and multi-high packets (SHA-256 a69e1eb2… and bb5bbedb…).
Compile the nine new modules in this order: OrderNineCohortAdjoint,
OrderNineCohortMoments, OrderNineCohortRankNine, OrderNineCohortGeometry,
OrderNineCohortSupport, OrderNineCohortRadauWeights, OrderNineCohortCompression,
OrderNineCohortRadauLate, OrderNineFiveFiveExclusion; then run
AuditReviewedNativeOrderNineFiveFive.lean. Autonomous proof audit shows only
propext, Classical.choice and Quot.sound.
