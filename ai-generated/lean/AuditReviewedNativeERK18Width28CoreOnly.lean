module

import RKCert.ReviewedNative.ERK18Width28Frontier

open RKResearch Module RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.ERK18

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 28) (Fin 28) K} {b : Fin 28 → K}

-- The primary width census, on the original reviewed strict tableau only.
example (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder 18 A b) :
    (finrank K (zeroSpace A 9) = 10 ∧ finrank K (back A b 0) = 0) ∨
    (finrank K (zeroSpace A 9) = 10 ∧ finrank K (back A b 0) = 1) ∨
    (finrank K (zeroSpace A 9) = 11 ∧ finrank K (back A b 0) = 0) := by
  rcases width28_actual_rank_frontier ha ho with h | h | h
  · exact Or.inl h.2
  · exact Or.inr (Or.inl h.2)
  · exact Or.inr (Or.inr h.2)

-- Literal measured saturation; still no terminal index hypothesis.
example (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder 18 A b)
    (h : 17 + finrank K (zeroSpace A 9) + finrank K (back A b 0) = 28) :
    back A b 7 = annih (treeSpace A 9) ∧
    primitiveBack A b 7 = annih (treeSpace A 9) ∧
    (∀ n ≤ 7, finrank K (back A b n) = finrank K (back A b 0) + n ∧
      back A b n = primitiveBack A b n) :=
  width28_saturated_reverse_flag ha ho h

end

#print axioms width28_actual_rank_frontier
#print axioms width28_saturated_reverse_flag
