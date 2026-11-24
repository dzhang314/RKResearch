module

public import RKCert.ReviewedNative.ERKGradeEightSurplus
public import RKCert.ReviewedNative.OptionalTerminalMark

@[expose] public section

/-! # Order nineteen, width twenty-nine: the genuine midpoint and next chart

Everything is measured on the original reviewed tableau. In the nonzero
first-adjoint case the degree-nine scalar band and grade-ten pure space
already fill the numerical grade-ten tree space. -/
namespace RKResearch.Certified.Graded
open RKResearch Module
open scoped Matrix

section PaidGrowth
variable {K : Type*} [Field K] {n p j : ℕ}
variable {A : Matrix (Fin n) (Fin n) K} {b : Fin n → K}

/-- The output's first moment suffices for strict forward growth, even
after scalar separation of the entire grade has ceased to hold. -/
theorem zeroSpace_strict_of_paid_output (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder p A b) (pos : 1≤j) (pay : j+2≤p) :
    zeroSpace A j < zeroSpace A (j+1) := by
  refine lt_of_le_of_ne (zeroSpace_mono A (Nat.le_succ _)) ?_
  intro eq
  have yes : diag (nodes A) 1 ∈ zeroSpace A j := by
    apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha)
    · intro w hw
      rw [eq]
      exact mat_zeroSpace ho j (by omega) hw
    · intro w hw
      rw [eq]
      exact diag_zeroSpace A j hw
    · rw [eq]
      exact zeroSpace_mono A (by omega : 2≤j+1) (forward_seed_mem A)
  have e : normTree A (clockTree 1) = diag (nodes A) 1 := by
    rw [normTree_clockTree]
    ext i
    simp
  have mass := probe_normTree ho (clockTree 1) 0 (by rw [order_clockTree]; omega)
  have dead := probe_zeroSpace (k:=0) ho (by omega) yes
  rw [e,dead,mul_zero] at mass
  exact zero_ne_one mass

end PaidGrowth
end RKResearch.Certified.Graded

namespace RKResearch.Certified.ERK19
open RKResearch Module Graded Graded.Reverse

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem surplus_nine {n : ℕ} {A : Matrix (Fin n) (Fin n) K} {b : Fin n→K}
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b) :
    10≤finrank K (zeroSpace A 9) := by
  have h8 := grade_eight_surplus_ordered_of_reviewed_order ha ho (by decide)
  have h := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_paid_output ha ho (j:=8) (by decide) (by decide))
  change finrank K (zeroSpace A 8)<finrank K (zeroSpace A 9) at h
  omega

theorem ordered_erk19_stage_floor29 {n : ℕ} {A : Matrix (Fin n) (Fin n) K} {b : Fin n→K}
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b) : 29≤n := by
  have d := surplus_nine ha ho
  have t := treeSpace_rank_eq_of_separation ho (q:=9) (by decide) (coeff_separated ho (by decide))
  have c := backward_endpoint_count ha ho 9 8 (by decide) (by decide)
  omega

variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

theorem ordered_width29_frame (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b) :
    OddBalancedFrame A b 9 2 ∧ LastActive b (Fin.last 28) := by
  refine ⟨odd_short_frame ha ho (by decide) (by decide) (by decide) (surplus_nine ha ho),?_,?_⟩
  · intro vanish
    have bound : 28≤29 := by decide
    have z (i : Fin 29) (h : 28 ≤ i.val) : b i=0 := by
      have e : i=Fin.last 28 := Fin.ext (by have := i.isLt; change i.val=28; omega)
      rwa [e]
    exact (by decide : ¬ 29≤28) (ordered_erk19_stage_floor29
      (prefix_strict_lower ha bound) (prefix_hasOrder_of_suffix_zero ha ho bound z))
  · intro i hi
    exact ((not_lt_of_ge (Fin.le_last i)) hi).elim

/-- On the nonzero-seed branch no rank hypothesis is supplied by the
caller: the scalar band through degree nine and all actual grade-ten
defects fill E10, and its ordinary defect rank is eleven. -/
theorem nonzero_seed_grade_ten (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b)
    (nz : firstSeed A b ≠ 0) :
    finrank K (zeroSpace A 10)=11 ∧ finrank K (treeSpace A 10)=21 ∧
      treeSpace A 10=(coeffEval A 9).range ⊔ zeroSpace A 10 := by
  have h9 := surplus_nine ha ho
  have g := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_of_paid_output ha ho (j:=9) (by decide) (by decide))
  change finrank K (zeroSpace A 9)<finrank K (zeroSpace A 10) at g
  have r := rank_coeff_sup_of_separated (zeroSpace A 10) (q:=9)
    (coeff_separated_next ha ho (by decide))
  have inc : (coeffEval A 9).range ⊔ zeroSpace A 10 ≤ treeSpace A 10 := by
    apply sup_le _ (zeroSpace_le_treeSpace A 10)
    rintro _ ⟨a,rfl⟩
    exact treeSpace_mono A (by decide : 9≤10) (coeffEval_mem_treeSpace A 9 a)
  have low := Submodule.finrank_mono inc
  change finrank K ((coeffEval A 9).range ⊔ zeroSpace A 10 : Submodule K (Fin 29 → K)) = 10 + finrank K (zeroSpace A 10) at r
  rw [r] at low
  have cap := backward_count ha ho 10 7 (by decide)
  rw [first_dim_one nz] at cap
  exact ⟨by omega,by omega,(Submodule.eq_of_le_of_finrank_le inc (by omega)).symm⟩

end RKResearch.Certified.ERK19
