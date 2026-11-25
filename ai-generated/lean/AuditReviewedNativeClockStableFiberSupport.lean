module

import RKCert.ReviewedNative.ClockStableFiberSupport

open Module RKCert.Endpoint RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open scoped BigOperators Classical

section
variable {K : Type*} [Field K] {s : ℕ}

example (c : Fin s → K) (W : Submodule K (Fin s → K)) (x : ClockSite c) :
    x ∈ clockFiberSupport c W ↔ clockFiberColumns c W x ≠ ⊥ :=
  mem_clockFiberSupport

example (c : Fin s → K) (W : Submodule K (Fin s → K)) (stable : W.map (diag c) ≤ W) :
    (∑ x : ClockSite c, finrank K (clockFiberColumns c W x)) = finrank K W :=
  sum_finrank_clockFiberColumns_eq_of_stable c W stable

example (c : Fin s → K) (W : Submodule K (Fin s → K)) (stable : W.map (diag c) ≤ W) :
    (clockFiberSupport c W).card ≤ finrank K W :=
  clockFiberSupport_card_le_finrank_of_stable c W stable

example (c : Fin s → K) (W : Submodule K (Fin s → K)) (maskStable : clockLocal c W = W)
    (dimW : finrank K W ≤ 2) : (clockFiberSupport c W).card ≤ 2 :=
  clockFiberSupport_card_le_two_of_stable c W ((clockLocal_eq_iff c W).mp maskStable) dimW

end

#print axioms RKResearch.Certified.Graded.Reverse.mem_clockFiberSupport
#print axioms RKResearch.Certified.Graded.Reverse.sum_finrank_clockFiberColumns_eq_of_stable
#print axioms RKResearch.Certified.Graded.Reverse.clockFiberSupport_card_le_finrank_of_stable
#print axioms RKResearch.Certified.Graded.Reverse.clockFiberSupport_card_le_two_of_stable
