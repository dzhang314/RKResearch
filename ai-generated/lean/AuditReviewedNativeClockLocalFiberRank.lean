module

import RKCert.ReviewedNative.ClockLocalFiberRank

open Module RKResearch.Certified.Graded.Reverse
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] {s : ℕ}
variable (c w : Fin s → K) (X : Submodule K (Fin s → K))

example : w ∈ clockLocal c (annih X) ↔
    ∀ x : ClockSite c, clockFiberRestrict c x w ∈ annih (clockFiberColumns c X x) :=
  mem_clockLocal_annih_iff

example : clockLocal c (annih X) ≃ₗ[K]
    ((x : ClockSite c) → ↥(annih (clockFiberColumns c X x))) :=
  clockLocalAnnihEquiv c X

example : finrank K (clockLocal c (annih X)) =
    ∑ x : ClockSite c, (Fintype.card (ClockFiber c x) - finrank K (clockFiberColumns c X x)) :=
  finrank_clockLocal_annih c X

example : finrank K (clockLocal c (annih X)) +
    (∑ x : ClockSite c, finrank K (clockFiberColumns c X x)) = s :=
  finrank_clockLocal_annih_add_sum_eq c X

end

#print axioms RKResearch.Certified.Graded.Reverse.clockLocalAnnihEquiv
#print axioms RKResearch.Certified.Graded.Reverse.finrank_clockLocal_annih
#print axioms RKResearch.Certified.Graded.Reverse.finrank_clockLocal_annih_add_sum_eq
