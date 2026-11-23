module

public import RKCert.Tree

@[expose] public section

/-!
# The explicit RK stage bound

After `n` applications of a strictly lower-triangular tableau, the first `n`
components are zero. Thus the `(s+1)`-vertex chain has zero output weight for
an `s`-stage explicit method. Its order condition would say `0 = 1`.
-/

namespace RKCert

variable {K : Type*} [CommSemiring K] {s : ℕ}
variable {A : Fin s → Fin s → K} {b : Fin s → K}

/-- A zero-based stage `i` cannot see a chain with more than `i` edges. -/
theorem stageWeight_chain_eq_zero (hA : StrictLower A) (n : ℕ) (i : Fin s)
    (hi : i.val < n) : stageWeight A (Tree.chain n) i = 0 := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [stageWeight_chain_succ]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hij : i.val ≤ j.val
    · rw [hA i j hij, zero_mul]
    · rw [ih j (by omega), mul_zero]

/-- Nilpotence on the chain; includes `s = 0` (the empty output sum). -/
theorem weight_chain_eq_zero (hA : StrictLower A) (n : ℕ) (hn : s ≤ n) :
    weight A b (Tree.chain n) = 0 := by
  unfold weight
  apply Finset.sum_eq_zero
  intro i _
  rw [stageWeight_chain_eq_zero hA n i (lt_of_lt_of_le i.isLt hn), mul_zero]

/-- An explicit `s`-stage tableau cannot satisfy the tree conditions beyond order `s`.
The proof needs only `0 ≠ 1`; it applies in particular over every characteristic-zero field. -/
theorem explicit_order_le_stages [Nontrivial K] {p : ℕ}
    (hA : StrictLower A) (hp : HasTreeOrderAtLeast A b p) : p ≤ s := by
  by_contra h
  have hc := chain_condition hp (n := s) (by omega)
  rw [weight_chain_eq_zero hA s (le_refl s), mul_zero] at hc
  exact zero_ne_one hc

end RKCert
