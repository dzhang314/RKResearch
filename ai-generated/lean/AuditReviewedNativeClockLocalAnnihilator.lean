module

import RKCert.ReviewedNative.ClockLocalAnnihilator

open RKCert.Endpoint RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

section
variable {K : Type*} [Field K] {s : ℕ}
variable (c w : Fin s → K) (P Q X : Submodule K (Fin s → K))

example : w ∈ clockLocal c P ↔ ∀ x : K, blockMask c x w ∈ P :=
  mem_clockLocal

example : clockLocal c P ≤ P ∧
    (clockLocal c P).map (diag c) ≤ clockLocal c P ∧
    (Q ≤ P → Q.map (diag c) ≤ Q → Q ≤ clockLocal c P) :=
  ⟨clockLocal_le c P, clockLocal_stable c P,
    fun inc stable => le_clockLocal_of_stable inc stable⟩

example : clockLocal c P = P ↔ P.map (diag c) ≤ P :=
  clockLocal_eq_iff c P

example : clockLocal c (annih (X ⊔ X.map (diag c))) = clockLocal c (annih X) :=
  clockLocal_annih_clockStep c X

end

#print axioms RKResearch.Certified.Graded.Reverse.le_clockLocal_of_stable
#print axioms RKResearch.Certified.Graded.Reverse.clockLocal_eq_iff
#print axioms RKResearch.Certified.Graded.Reverse.clockLocal_annih_clockStep
