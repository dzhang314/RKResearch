module

public import RKCert.ReviewedNative.ERKGradeEightOffCore
public import RKCert.ReviewedNative.ERKGradeEightQuartic
public import RKCert.ReviewedNative.ERK17WidthFrame

@[expose] public section

/-! # The uniform ordered grade-eight surplus, with the reviewed ERK17 floor

This theorem finishes the forward surplus at order at least sixteen.
It is not an exclusion of the width-26 reverse/hidden cases. -/
namespace RKResearch.Certified.Graded
open RKResearch Module

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n p : ℕ} {A : Matrix (Fin n) (Fin n) K} {b : Fin n → K}

theorem grade_eight_surplus_ordered_of_reviewed_order
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b p) (pay : 16≤p) :
    9≤finrank K (zeroSpace A 8) := by
  by_contra! bad
  have cap : finrank K (zeroSpace A 8)≤8 := by omega
  cases n with
  | zero =>
      obtain ⟨i,_⟩ := Reverse.exists_lastActive ho (by omega)
      exact Fin.elim0 i
  | succ s =>
      obtain ⟨_,r,U,w,chart⟩ := ordered_grade_eight_quartic_only ha ho pay cap
      obtain ⟨P,i,j,ports⟩ := grade_four_flat_quartic_ports ha ho pay chart
      exact ports.impossible_ordered

end RKResearch.Certified.Graded

namespace RKResearch.Certified.ERK17
open RKResearch Module RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The exact native stage floor used by the width-26 split. -/
theorem ordered_erk17_stage_floor26 {n : ℕ} {A : Matrix (Fin n) (Fin n) K} {b : Fin n → K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b 17) : 26≤n :=
  width_floor_of_grade_eight ha ho (grade_eight_surplus_ordered_of_reviewed_order ha ho (by decide))

theorem ordered_width26_full_frame {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b 17) :
    OddBalancedFrame A b 8 2 ∧ LastActive b (Fin.last 25) :=
  ⟨width26_frame ha ho (grade_eight_surplus_ordered_of_reviewed_order ha ho (by decide)),
    width26_last_live_of_uniform_surplus ha ho
      (fun h₁ h₂ => grade_eight_surplus_ordered_of_reviewed_order h₁ h₂ (by decide))⟩

end RKResearch.Certified.ERK17
