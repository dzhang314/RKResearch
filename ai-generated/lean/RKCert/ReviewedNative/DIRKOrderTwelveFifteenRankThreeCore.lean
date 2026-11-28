module

public import RKCert.ReviewedNative.DIRKOrderTwelveFifteenReverseRanks

@[expose] public section

/-! Actual paid cubic-power probes and the terminal-zero reverse rank
alternative on the f₅ = 3 DIRK order-twelve equality face. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen

open RKResearch Module Reverse
open scoped Matrix BigOperators

set_option maxHeartbeats 4000000

section PureMoments
variable {K : Type*} [CommRing K]
    {A : Matrix (Fin 15) (Fin 15) K} {b : Fin 15 → K}

/-- The denominator-cleared primitive defect is three times the cubic defect. -/
theorem paidFirstCubicPower (ho : HasOrder 12 A b) {k : ℕ} (hk : k ≤ 8) :
    probe A b k (monomialStageDefect A 2) = 0 :=
  probe_zeroSpace ho (by omega : k+3+1≤12) (monomialStageDefect_mem A 2)

/-- Squared cubic defects are genuine pure grade six. -/
theorem paidSecondCubicPower (ho : HasOrder 12 A b) {k : ℕ} (hk : k ≤ 5) :
    probe A b k (monomialStageDefect A 2 ^ 2) = 0 := by
  have h := monomialStageDefect_mem A 2
  have sq : monomialStageDefect A 2 ^ 2 ∈ zeroSpace A 6 := by
    rw [pow_two]
    exact zeroSpace_mul h h
  exact probe_zeroSpace ho (by omega : k+6+1≤12) sq

/-- Cubed cubic defects are genuine pure grade nine. -/
theorem paidThirdCubicPower (ho : HasOrder 12 A b) {k : ℕ} (hk : k ≤ 2) :
    probe A b k (monomialStageDefect A 2 ^ 3) = 0 := by
  have h := monomialStageDefect_mem A 2
  have h2 : monomialStageDefect A 2 ^ 2 ∈ zeroSpace A 6 := by
    rw [pow_two]
    exact zeroSpace_mul h h
  have h3 : monomialStageDefect A 2 ^ 3 ∈ zeroSpace A 9 := by
    change monomialStageDefect A 2 ^ (2+1) ∈ zeroSpace A 9
    rw [pow_succ]
    exact zeroSpace_mul h2 h
  exact probe_zeroSpace ho (by omega : k+9+1≤12) h3

/-- Inclusive opposing supports pay a literal zero pairing after one real
lower triangular multiplication, without any diagonal hypothesis. -/
theorem crossedPrimitiveZero (ha : A.IsLowerTriangular)
    (t : Fin 15) {v w : Fin 15 → K}
    (vf : ∀ i ≤ t, v i = 0) (wb : ∀ i, t ≤ i → w i = 0) :
    row w (mat A v) = 0 := by
  classical
  rw [row_apply, dotProduct]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hit : i ≤ t
  · have zz : mat A v i = 0 := by
      rw [mat_apply, Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hji : j ≤ i
      · simp [vf j (hji.trans hit)]
      · rw [ha (lt_of_not_ge hji), zero_mul]
    rw [zz, mul_zero]
  · rw [wb i (le_of_lt (lt_of_not_ge hit)), zero_mul]

end PureMoments

section ReverseRanks
variable {K : Type*} [Field K]
    {A : Matrix (Fin 15) (Fin 15) K} {b : Fin 15 → K}

theorem rankThreeFaceReverseAlternative
    (ha : A.IsLowerTriangular) (ho : HasOrder 12 A b)
    (H : EqualityFrame A b) (live : b (Fin.last 14) ≠ 0)
    (f5 : finrank K (zeroSpace A 5) = 3) :
    (finrank K (primitiveBack A b 5) = 4) ∨
    (finrank K (primitiveBack A b 5) = 5 ∧
      primitiveBack A b 5 = zeroAt (annih (treeSpace A 5)) (Fin.last 14)) := by
  obtain ⟨inc, cap⟩ := equality_reverse_six_cap ha ho H live
  rw [f5] at cap
  have gain := dirk_primitiveBack_rank_gain ha ho (r:=1) (n:=5) (by decide) (by decide) (by decide)
  have lower : 4 ≤ finrank K (primitiveBack A b 5) := by omega
  by_cases rb : finrank K (primitiveBack A b 5) = 4
  · exact Or.inl rb
  · refine Or.inr ⟨by omega, ?_⟩
    have debit := finrank_zeroAt_annih (treeSpace A 5) _ H.lastOutFive
    have ann := finrank_annih (treeSpace A 5)
    rw [Fintype.card_fin] at ann
    have t5 := treeSpace_rank_eq_of_separation ho (q:=5) (by decide) (coeff_separated ho (by decide))
    rw [f5] at t5
    exact Submodule.eq_of_le_of_finrank_le inc (by omega)

end ReverseRanks

#print axioms paidFirstCubicPower
#print axioms paidSecondCubicPower
#print axioms paidThirdCubicPower
#print axioms crossedPrimitiveZero
#print axioms rankThreeFaceReverseAlternative

end RKResearch.Certified.Graded.OrderTwelveFifteen
