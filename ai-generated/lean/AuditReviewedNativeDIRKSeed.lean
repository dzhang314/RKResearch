import RKCert.ReviewedNative.DIRKSeedReduction

open RKResearch RKResearch.Certified.Graded
open scoped Matrix

#print axioms RKResearch.Certified.Graded.mem_of_invariant_dirk_two_seeds
#print axioms RKResearch.Certified.Graded.transpose_mat_pivot
#print axioms RKResearch.Certified.Graded.forward_dirk_seeds_force_nodes
#print axioms RKResearch.Certified.Graded.reverse_dirk_seeds_force_clock

example {K : Type*} [Field K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (h : HasOrder 6 A b) (ha : A.IsLowerTriangular) (U : Submodule K (Fin s → K))
    (hN : ∀ x ∈ U, mat A x ∈ U) (hY : ∀ x ∈ U, diag (nodes A) x ∈ U)
    (h₂ : monomialStageDefect A 1 ∈ U) (h₃ : monomialStageDefect A 2 ∈ U)
    (hquiet : ∀ x ∈ U, probe A b 0 x = 0) : False := by
  have hz := hquiet _ (forward_dirk_seeds_force_nodes ha U hN hY h₂ h₃)
  have he : probe A b 0 (nodes A) = stageMass b (nodes A) 1 := by
    simp only [probe, row_apply, pow_zero, mul_one, stageMass, pow_one]
  have hp := h.bushy_moment 1 (by decide)
  rw [he] at hz
  change ((1+1 : ℕ) : K) * stageMass b (nodes A) 1 = 1 at hp
  rw [hz, mul_zero] at hp
  exact zero_ne_one hp

example {K : Type*} [Field K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (h : HasOrder 6 A b) (ha : A.IsLowerTriangular) (U : Submodule K (Fin s → K))
    (hN : ∀ x ∈ U, mat A.transpose x ∈ U)
    (hY : ∀ x ∈ U, diag (reflectedClock A) x ∈ U)
    (h₂ : reflectedStageRow A b 1 ∈ U) (h₃ : reflectedStageRow A b 2 ∈ U)
    (hquiet : ∀ x ∈ U, row x 1 = 0) : False := by
  have hz := hquiet _ (reverse_dirk_seeds_force_clock ha U hN hY h₂ h₃)
  have he : row (diag (reflectedClock A) b) 1 =
      stageMass b (nodes A) 0 - stageMass b (nodes A) 1 := by
    simp only [row_apply, dotProduct, stageMass, diag_apply, Pi.one_apply, mul_one,
      reflectedClock, Pi.sub_apply, pow_zero, pow_one, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have m0 := h.bushy_moment 0 (by decide)
  have m1 := h.bushy_moment 1 (by decide)
  norm_num only [Nat.reduceAdd, Nat.cast_one, Nat.cast_ofNat, one_mul] at m0 m1
  have hp : (2:K)*(stageMass b (nodes A) 0 - stageMass b (nodes A) 1) = 1 := by
    linear_combination 2*m0-m1
  rw [he] at hz
  rw [hz, mul_zero] at hp
  exact zero_ne_one hp
