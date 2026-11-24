import RKCert.ReviewedNative.ERKGradeEightSurplus

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.ERK17 Module Polynomial

-- Arbitrary characteristic-zero fields retain the actual exceptional ratio.
example {K : Type*} [Field K] [CharZero K] {s p r : ℕ}
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
    {U : Submodule K (Fin (s+1)→K)} {w : Fin (s+1)→K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b) (pay : 16≤p)
    (H : FlatClockHead A 4 4 r U w) :
    ∃ i j : Fin (s+1), 15*(nodes A j/nodes A i)^2-24*(nodes A j/nodes A i)+10=0 := by
  obtain ⟨_,i,j,ports⟩ := grade_four_flat_quartic_ports ha ho pay H
  exact ⟨i,j,ports.exceptional_ratio⟩

-- A direct reviewed endpoint client. No width-26 exclusion is asserted.
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 17 A b) : 26≤s :=
  ordered_erk17_stage_floor26 ha ho

#print axioms RKResearch.Certified.Graded.grade_four_flat_quartic_ports
#print axioms RKResearch.Certified.Graded.Quartic3Plus2.exceptional_ratio
#print axioms RKResearch.Certified.Graded.Quartic3Plus2.impossible_ordered
#print axioms RKResearch.Certified.Graded.grade_eight_surplus_ordered_of_reviewed_order
#print axioms RKResearch.Certified.ERK17.ordered_erk17_stage_floor26
#print axioms RKResearch.Certified.ERK17.ordered_width26_full_frame
