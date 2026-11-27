module

public import RKCert.ReviewedNative.TailMatrixReceipts

@[expose] public section

/-! A protected chronological receiver may have one more local grade
than is needed on the whole block. It is exported as an actual physical
donor for the next symbolic continuation. -/

namespace RKResearch.Certified.TwoOrderMomentTail

open FiniteRootedTree TwoDonorDense
open scoped Matrix FiniteRootedTree BigOperators

variable {ι η K : Type*} [Fintype ι] [Fintype η] [Field K] [CharZero K]

theorem protected_pure {q : ℕ} (hq : 1 ≤ q)
    {A : Matrix ι ι K} {U : Matrix η ι K} {B : Matrix η η K} {c : η → K}
    (hfeed : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q →
      U *ᵥ normalized A t + B *ᵥ (c^((t.order : ℕ)-1)) =
      ((1 / (t.order : K)) : K) • c^(t.order : ℕ))
    (i : η)
    (htop : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q+1 →
      (U *ᵥ normalized A t + B *ᵥ (c^((t.order : ℕ)-1))) i =
      c i ^ (t.order : ℕ) / (t.order : K)) :
    PureAt (tableau A U B) (Sum.inr i) (q+2) := by
  have hc := congrFun (tail_clocks_from_feed hq hfeed) i
  change clocks (tableau A U B) (Sum.inr i) = c i at hc
  intro t ht
  rw [hc]
  cases t with
  | leaf => simp [normalized_leaf, order]
  | butcherProduct t u =>
    have hT := t.order.pos
    have hU := u.order.pos
    have hs : ((t ◂ u).order : ℕ) = (t.order : ℕ)+(u.order : ℕ) := rfl
    have he : ((t ◂ u).order : ℕ)-1 = (t.order : ℕ)-1+(u.order : ℕ) := by omega
    have hne : (u.order : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have heval : (u.order : K) * (c i ^ (u.order : ℕ)/(u.order : K)) = c i ^ (u.order : ℕ) := by
      rw [mul_comm, div_mul_cancel₀ _ hne]
    rw [normalized_join]
    change (tail (normalized (tableau A U B) t) *
      ((u.order : K) • tail (tableau A U B *ᵥ normalized (tableau A U B) u))) i = _
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [low_pure hfeed t (by omega), tail_action, head_normalized,
      low_pure hfeed u (by omega), htop u (by omega)]
    simp only [Pi.pow_apply]
    rw [heval, he, pow_add]

/-- A matrix with two chronological groups of observation rows. -/
def combineRows {ρ σ τ : Type*} (O : Matrix ρ τ K) (P : Matrix σ τ K) :
    Matrix (ρ ⊕ σ) τ K := fun i j => Sum.elim O P i j

omit [CharZero K] in
/-- A head row with zero taps on the old strict-predecessor receipts
may use the full extra degree of the mixed observation rows alone. -/
theorem protected_bank_action {ρ σ : Type*} [Fintype ρ] [Fintype σ]
    {n : ℕ} {i : η} {x : ι → K} {j : Fin n}
    (F : Matrix η (ρ ⊕ σ) K)
    (O : Matrix ρ ι K) (P : Matrix σ ι K)
    (E : Matrix ρ (Fin n) K) (D : Matrix σ (Fin n) K)
    (hzero : ∀ k, F i (Sum.inr k) = 0)
    (hobs : O *ᵥ x = E.col j) :
    ((F * combineRows O P) *ᵥ x) i =
      (F * combineRows E D) i j := by
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, Matrix.mul_apply, dotProduct, Fintype.sum_sum_type, combineRows,
    hzero, zero_mul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  have hh := congrFun hobs k
  change (∑ m, O k m * x m) = E k j at hh
  change F i (Sum.inl k) * (∑ m, O k m * x m) = F i (Sum.inl k) * E k j
  exact congrArg (fun u => F i (Sum.inl k)*u) hh

#print axioms protected_pure
#print axioms protected_bank_action
end RKResearch.Certified.TwoOrderMomentTail
