module

public import RKCert.ReviewedNative.ERK8CharElevenFiveCofactor
public import RKCert.ReviewedNative.ERK8CharElevenFiveWeights

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The later quadratic clean row is physical stage 8. The first
reflected seed has a nonzero cofactor scale at that row. Once the
four early off rows are known, no affine J2 profile is needed. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

open RKResearch Polynomial Module OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open RKResearch.Certified.Graded.ERK8CharEleven Reverse
open scoped Classical Matrix BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

theorem reflected_first_diagonal_if_later_zero (ha : ∀ i j, i≤j → A i j=0) (i : Fin 10)
    (later : ∀ j, i<j → reflectedStageWeight A b 1 j=0) :
    reflectedStageRow A b 1 i=-(b i*(1-nodes A i)^2) := by
  have e : (Aᵀ *ᵥ reflectedStageWeight A b 1) i=0 := by
    change (∑ j,A j i*reflectedStageWeight A b 1 j)=0
    apply Finset.sum_eq_zero
    intro j _
    by_cases l : j ≤ i
    · rw [ha j i l,zero_mul]
    · rw [later j (lt_of_not_ge l),mul_zero]
  simp only [reflectedStageRow,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,e,mul_zero,zero_sub,
    reflectedStageWeight,reflectedClock,Pi.sub_apply,Pi.one_apply]

theorem after_later_clean_reflected_weight_zero
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (five : (offKnots A).card=5) {theta : K} (H : ExceptionalHead A theta)
    {x z : Fin 10} (T : FiveCleanTail A x z) :
    ∀ j, z<j → reflectedStageWeight A b 1 j=0 := by
  intro j zj
  have zl : (6:Fin 10)≤z := by
    rcases lateRows_which T.z_late with h|h|h <;> rw [h] <;> decide
  have lj := zl.trans_lt zj
  by_cases gj : g A j=0
  · rcases (T.clean_iff j).mp gj with m|e|e
    · simp only [anchorRows,Finset.mem_insert,Finset.mem_singleton] at m
      rcases m with h|h|h
      · exact ((by decide : ¬ ((6:Fin 10)<0)) (h ▸ lj)).elim
      · exact ((by decide : ¬ ((6:Fin 10)<4)) (h ▸ lj)).elim
      · change b j*(1-nodes A j)^1=0
        rw [h,show nodes A 9=1 from H.terminal_clock]
        simp
    · exact ((ne_of_lt (T.xz.trans zj)) e.symm).elim
    · exact ((ne_of_lt zj) e.symm).elim
  · rw [show reflectedStageWeight A b 1 j=b j*(1-nodes A j)^1 from rfl,
      five_off_weights_are_zero ha ho five H j gj,zero_mul]

/-- Earned last clean physical placement for the only two late cases. -/
theorem five_later_clean_is_eight
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (five : (offKnots A).card=5) (cleanFive : (cleanKnots A).card=5)
    {theta : K} (H : ExceptionalHead A theta) (S : CenterPrefix A 4)
    {x z : Fin 10} (T : FiveCleanTail A x z) :
    z=8 ∧ (x=6 ∨ x=7) := by
  have later := after_later_clean_reflected_weight_zero ha ho five H T
  have bz := (clean_quadratic_weights_equal_nonzero ha ho p five H S T).2
  have y : 1-nodes A z=nodes A x := by linear_combination -T.sum_one
  have xne : nodes A x≠0 := by
    intro e
    have n8 : (8:K)≠0 := (ho.natCast_isUnit (n:=8) (by decide) (by decide)).ne_zero
    exact n8 (by simpa [e] using T.prod_eight.symm)
  have Jz : reflectedStageRow A b 1 z≠0 := by
    rw [reflected_first_diagonal_if_later_zero ha z later,y]
    exact neg_ne_zero.mpr (mul_ne_zero bz (pow_ne_zero _ xne))
  obtain ⟨rho,h⟩ := first_reflected_bulk_multiple ha ho p five cleanFive H S T
  have rn : rho≠0 := by
    intro r
    exact Jz (by rw [h,r,zero_smul]; rfl)
  have Jnz (i : Fin 10) (hi : i∈bulkRows) : reflectedStageRow A b 1 i≠0 := by
    rw [h,Pi.smul_apply,smul_eq_mul]
    exact mul_ne_zero rn (bulkReverse_ne_at A hi)
  have z8 : z=8 := by
    by_contra n
    have zl : z<8 := by
      rcases lateRows_which T.z_late with h6|h7|h8
      · rw [h6]; decide
      · rw [h7]; decide
      · exact (n h8).elim
    have g8 : g A 8≠0 := by
      intro e
      rcases (T.clean_iff 8).mp e with e|e|e
      · exact (by decide : (8:Fin 10)∉anchorRows) e
      · exact (ne_of_lt (T.xz.trans zl)) e.symm
      · exact (ne_of_lt zl) e.symm
    have b8 := five_off_weights_are_zero ha ho five H 8 g8
    have J0 := reflected_first_diagonal_if_later_zero ha (8:Fin 10) (fun j hj=>later j (zl.trans hj))
    rw [b8,zero_mul,neg_zero] at J0
    exact Jnz 8 (by decide) J0
  have x67 : x=6∨x=7 := by
    rcases lateRows_which T.x_late with h6|h7|h8
    · exact Or.inl h6
    · exact Or.inr h7
    · exact ((ne_of_lt T.xz) (h8.trans z8.symm)).elim
  exact ⟨z8,x67⟩

end RKResearch.Certified.Graded.ERK8CharEleven.FiveOff

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.FiveOff.five_later_clean_is_eight
