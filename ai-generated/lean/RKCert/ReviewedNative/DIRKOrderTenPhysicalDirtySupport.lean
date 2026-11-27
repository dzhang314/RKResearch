module

public import RKCert.ReviewedNative.DIRKOrderTenSaturation
public import RKCert.ReviewedNative.DIRKPrefixHermite
public import RKCert.ReviewedNative.WeightedClockBand

@[expose] public section

/-! # Physical (not output-active) DIRK10 cubic-defect clocks

The dirty support includes every nonzero defect, even when the output
weight is zero.  Exactly two or three dirty labels would saturate a
native forward grade by a complete clock-invariant evaluation orbit,
contradicting the genuine inclusive DIRK Hermite rank gains. -/

namespace RKResearch.Certified.Graded.CrossedOrderTen

open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Matrix Classical

noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

private theorem weighted_band_of_forward_seed {v : Fin s → K} {j : ℕ}
    (seed : v ∈ zeroSpace A j) (n : ℕ) :
    weightedBand (nodes A) v (n+1) ≤ zeroSpace A (j+n) := by
  let W := weightedEval (nodes A) v
  have powers (k : ℕ) : W (X^k) ∈ zeroSpace A (j+k) := by
    induction k with
    | zero =>
      have e : W 1 = v := by ext i; simp [W]
      simpa only [pow_zero,e,Nat.add_zero] using seed
    | succ k ih =>
      have z := diag_zeroSpace A (j+k) ih
      have e : diag (nodes A) (W (X^k)) = W (X^(k+1)) := by
        ext i
        simp only [diag_apply,W,weightedEval_apply,eval_pow,eval_X]
        rw [pow_succ']
        ring
      change diag (nodes A) (W (X^k)) ∈ zeroSpace A (j+k+1) at z
      rw [e] at z
      exact z
  intro w hw
  obtain ⟨P,d,rfl⟩ := mem_weightedBand.mp hw
  by_cases z : P=0
  · rw [z,map_zero]
    exact (zeroSpace A (j+n)).zero_mem
  have deg : P.natDegree < n+1 := (natDegree_lt_iff_degree_lt z).mpr d
  change W P ∈ _
  rw [P.as_sum_range' (n+1) deg,map_sum]
  apply Submodule.sum_mem
  intro k hk
  rw [←C_mul_X_pow_eq_monomial,←smul_eq_C_mul,map_smul]
  exact (zeroSpace A (j+n)).smul_mem _ (zeroSpace_mono A
    (by have := Finset.mem_range.mp hk; omega) (powers k))

private theorem invariant_of_tight_band {v : Fin s → K} {j k : ℕ}
    (included : weightedBand (nodes A) v k ≤ zeroSpace A j)
    (sites : (weightedSites (nodes A) v).card = k)
    (rank : finrank K (zeroSpace A j) = k) :
    ∀ w ∈ zeroSpace A j, diag (nodes A) w ∈ zeroSpace A j := by
  have e : weightedBand (nodes A) v k = zeroSpace A j := by
    apply Submodule.eq_of_le_of_finrank_le included
    rw [weightedBand_rank _ _ _ sites.ge,rank]
  have full : zeroSpace A j = (weightedEval (nodes A) v).range :=
    e.symm.trans (weightedBand_eq_range _ _ _ sites.le)
  intro w hw
  rw [full] at hw ⊢
  exact weighted_range_clock _ _ hw

variable [CharZero K] {A : Matrix (Fin 11) (Fin 11) K} {b : Fin 11 → K}

/-- A true eleven-stage order-ten DIRK cannot have precisely two or
three physical dirty clock values, even with unweighted dirty rows and
even if clean rows share those clock values. -/
theorem physical_dirty_count_ne_two_three
    (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) :
    let d := (weightedSites (nodes A) (monomialStageDefect A 2)).card
    d ≠ 2 ∧ d ≠ 3 := by
  let g := monomialStageDefect A 2
  let d := (weightedSites (nodes A) g).card
  change d ≠ 2 ∧ d ≠ 3
  have S := saturated ha ho
  have equality := treeSpace_rank_eq_of_separation ho (q:=4) (by decide)
    (coeff_defect_separated_paid ho (by decide) (by decide))
  have rank4 : finrank K (zeroSpace A 4) = 2 := by
    have := S.e4
    omega
  have rank5 := S.f5
  have seed : g ∈ zeroSpace A 3 := monomialStageDefect_mem A 2
  constructor
  · intro two
    have band : weightedBand (nodes A) g 2 ≤ zeroSpace A 4 :=
      weighted_band_of_forward_seed seed 1
    have gain := dirk_forward_invariant_outgoing (j:=4) ha ho (by decide)
      (zeroSpace A 4) le_rfl (invariant_of_tight_band band two rank4)
    change finrank K (zeroSpace A 4) + 2 ≤ finrank K (zeroSpace A 5) at gain
    omega
  · intro three
    have band : weightedBand (nodes A) g 3 ≤ zeroSpace A 5 :=
      weighted_band_of_forward_seed seed 2
    have gain := dirk_forward_invariant_incoming (j:=4) ha ho (by decide)
      (invariant_of_tight_band band three rank5)
    change finrank K (zeroSpace A 4) + 2 ≤ finrank K (zeroSpace A 5) at gain
    omega

/-- The actual physical dirty clock set is nonempty, and if it is not
a singleton, it has at least four distinct numerical labels. -/
theorem physical_dirty_count_one_or_at_least_four
    (ha : A.IsLowerTriangular) (ho : HasOrder 10 A b) :
    let d := (weightedSites (nodes A) (monomialStageDefect A 2)).card
    d = 1 ∨ 4 ≤ d := by
  let g := monomialStageDefect A 2
  let d := (weightedSites (nodes A) g).card
  change d = 1 ∨ 4 ≤ d
  have S := saturated ha ho
  have nz : g ≠ 0 := (dirk_grade_three_of_C2 ha ho (by decide) S.c2).1
  have atLeastOne : 0 < d := by
    have e : ∃ i, g i ≠ 0 := by
      by_contra! empty
      exact nz (funext empty)
    obtain ⟨i,hi⟩ := e
    exact Finset.card_pos.mpr ⟨nodes A i,mem_weightedSites.mpr ⟨i,hi,rfl⟩⟩
  obtain ⟨two,three⟩ := physical_dirty_count_ne_two_three ha ho
  change d ≠ 2 at two
  change d ≠ 3 at three
  omega

end
end RKResearch.Certified.Graded.CrossedOrderTen
