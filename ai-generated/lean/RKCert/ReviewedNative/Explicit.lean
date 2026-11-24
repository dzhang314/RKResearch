module

public import RKResearch.OrderConditions

public section

/-! Native explicit stage floor using the reviewed matrix-power chain formula. -/

namespace RKResearch.Certified

open FiniteRootedTree
open scoped Matrix

variable {R : Type*} [CommSemiring R] {s : ℕ}

private theorem pow_mulVec_apply_eq_zero {A : Matrix (Fin s) (Fin s) R}
    (ha : ∀ i j : Fin s, i ≤ j → A i j = 0) (v : Fin s → R)
    (n : ℕ) (i : Fin s) (hi : i.val < n) : ((A ^ n) *ᵥ v) i = 0 := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_apply_eq_sum]
      apply Finset.sum_eq_zero
      intro j _
      by_cases h : i ≤ j
      · rw [ha i j h, zero_mul]
      · have hj : j.val < i.val := lt_of_not_ge h
        rw [ih j (by omega), mul_zero]

/-- A tall tree has zero weight at a stage with too few available earlier rows. -/
theorem phi_tallTree_eq_zero {A : Matrix (Fin s) (Fin s) R}
    (ha : ∀ i j : Fin s, i ≤ j → A i j = 0) (n : ℕ+) (i : Fin s)
    (hi : i.val + 1 < (n : ℕ)) : Φ (tallTree n) A i = 0 := by
  rw [Φ_tallTree]
  exact pow_mulVec_apply_eq_zero ha 1 _ i (by omega)

/-- The explicit order barrier, directly over the reviewed order conditions. -/
theorem explicit_order_le_stages [Nontrivial R] {p : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (ha : ∀ i j : Fin s, i ≤ j → A i j = 0)
    (ho : HasOrder A b p) : p ≤ s := by
  by_contra h
  have hsp : s + 1 ≤ p := by omega
  let n : ℕ+ := ⟨s + 1, Nat.succ_pos s⟩
  have htree : ((tallTree n).order : ℕ) ≤ p := by
    rw [order_tallTree]
    exact hsp
  have hz : b ⬝ᵥ Φ (tallTree n) A = 0 := by
    unfold dotProduct
    apply Finset.sum_eq_zero
    intro i _
    have his := i.isLt
    rw [phi_tallTree_eq_zero ha n i (show i.val + 1 < s + 1 by omega), mul_zero]
  have hc := ho (tallTree n) htree
  rw [hz, mul_zero] at hc
  exact zero_ne_one hc

end RKResearch.Certified
