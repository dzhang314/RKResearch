module

public import RKCert.ReviewedNative.ERK8CharElevenFiveEarlyFiveExclusion
public import RKCert.ReviewedNative.ERK8CharElevenFiveTailScalar

@[expose] public section

/-! The entire characteristic-eleven five-off branch is impossible on
the literal original width-ten reviewed order predicate. Together with
the seven-off proof this leaves the same one/four census in every field. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField
open scoped Classical Matrix

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem no_five_off_char11
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0) :
    (offKnots A).card≠5 := by
  intro five
  have cleanFive := FiveOff.five_clean_of_literal ha ho five
  obtain ⟨theta,i,H,C⟩ := FiveOff.center_prefix_of_literal ha ho p five cleanFive
  rcases FiveOff.high_center_four_or_five ha ho p five cleanFive H C with h|h
  · have CS : FiveOff.CenterPrefix A 4 := h ▸ C
    obtain ⟨c5,g5,beta,bn,V,rem⟩ := FiveOff.five_off_early_chart_of_center_four ha ho p five cleanFive H CS
    obtain ⟨x,z,T⟩ := FiveOff.five_clean_tail_of_center_four five cleanFive H CS g5
    obtain ⟨z8,x67⟩ := FiveOff.five_later_clean_is_eight ha ho p five cleanFive H CS T
    have D : FiveOff.FiveCleanTail A x 8 := z8 ▸ T
    rcases x67 with x6|x7
    · exact FiveOff.five_off_tail_at_six_impossible ha ho p five cleanFive H CS (x6 ▸ D) g5 bn rem
    · exact FiveOff.five_off_tail_at_seven_impossible ha ho p five cleanFive H CS (x7 ▸ D) g5 c5 bn rem
  · exact FiveOff.five_off_contradiction_of_center_five ha ho p five cleanFive H (h ▸ C)

/-- This census needs no characteristic, order, or root-splitting guard
on the field of coefficients. The remaining one/four branches are not
excluded by this theorem. -/
theorem order8_paid_only_one_or_four_off
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) :
    (offKnots A).card=1 ∨ ((offKnots A).card=4 ∧ (cleanKnots A).card=5) := by
  rcases order8_paid_only_one_four_or_five_off ha ho with h|h|⟨p,h,_⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (no_five_off_char11 ha ho p h).elim

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.no_five_off_char11
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.order8_paid_only_one_or_four_off
