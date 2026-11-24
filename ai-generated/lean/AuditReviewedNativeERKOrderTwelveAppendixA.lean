module
import RKCert.ReviewedNative.ERKOrderTwelveAppendixA

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.ERK12 Module

section OriginalStages
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j=0) (h : HasOrder A b 12) (cap : s≤17)

example : treeSpace A 10=⊤ := actual_e10_top ha h cap
end OriginalStages

section ExactReverseLine
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i j, i ≤ j → A i j=0) (h : HasOrder A b 12) (cap : s+1≤17)
example : ¬(back A b 1).map (diag (reflectedClock A))≤back A b 1 :=
  back_one_noninvariant ha h (saturation_of_order ha h cap)
example : ¬(treeSpace A 9).map (diag (nodes A))≤treeSpace A 9 :=
  saturated_e9_escape ha h (saturation_of_order ha h cap)
end ExactReverseLine

#print axioms TwoNode.two_node_confinement
#print axioms reverse_first_pivot
#print axioms localized_reverse_chart
#print axioms localized_reverse_rows
#print axioms reflected_active_avoid
#print axioms reduce_reverse_rows
#print axioms back_one_noninvariant
#print axioms saturated_e9_escape
#print axioms saturated_e10_top
#print axioms actual_e10_top
