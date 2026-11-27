module

public import RKCert.ReviewedNative.PureStageAppend

@[expose] public section

/-!
# A literal pure append from a single paid shifted jet

A full dense decoder is sufficient but not necessary. A linear read of
old data realizing just the required clock's shifted polynomial
functional gives the same genuine local order at the new physical row.
-/
namespace RKResearch.Certified.TwoDonorDense

open FiniteRootedTree
open scoped Matrix FiniteRootedTree BigOperators

variable {ι K : Type*} [Fintype ι] [Field K] [CharZero K]

/-- Exactly the strict predecessor values needed for one pure row with
clock `x` and its own separate physical diagonal `γ`. -/
def PaidShiftedJet (A : Matrix ι ι K) (v : ι → K) (x γ : K) (q : ℕ) : Prop :=
  ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q →
    v ⬝ᵥ normalized A t =
      x^(t.order : ℕ)/(t.order : K)-γ*x^((t.order : ℕ)-1)

theorem paid_append_clock {A : Matrix ι ι K} {v : ι → K} {x γ : K} {q : ℕ}
    (hq : 1 ≤ q) (hv : PaidShiftedJet A v x γ q) :
    clocks (appendStage A v γ) (Sum.inr PUnit.unit) = x := by
  unfold clocks
  rw [append_mulVec_new]
  change v ⬝ᵥ (1 : ι → K) + γ*1 = x
  rw [← normalized_leaf A, hv leaf (by simpa [order] using hq)]
  simp [order]

/-- A local order gain from the actual predecessor row. This does not
assume any full polynomial decoder at the previous stage count. -/
theorem paid_append_pure {A : Matrix ι ι K} {v : ι → K} {x γ : K} {q : ℕ}
    (hq : 1 ≤ q) (hv : PaidShiftedJet A v x γ q) :
    PureAt (appendStage A v γ) (Sum.inr PUnit.unit) (q+1) := by
  intro t ht
  rw [paid_append_clock hq hv]
  induction t with
  | leaf => simp [normalized_leaf, order]
  | butcherProduct t u ihT ihU =>
    have hpT := t.order.pos
    have hpU := u.order.pos
    have hs : ((t ◂ u).order : ℕ) = (t.order : ℕ)+(u.order : ℕ) := rfl
    have hu : (u.order : ℕ) ≤ q := by omega
    have hexp : ((t ◂ u).order : ℕ)-1 = ((t.order : ℕ)-1)+(u.order : ℕ) := by omega
    have hne : (u.order : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcancel : (u.order : K) * (x^(u.order : ℕ)/(u.order : K)) = x^(u.order : ℕ) := by
      rw [mul_comm, div_mul_cancel₀ _ hne]
    rw [normalized_join]
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [ihT (by omega), append_mulVec_new, append_normalized_old, hv u hu,
      ihU (by omega), sub_add_cancel, hcancel, hexp, pow_add]

/-- Two coefficient rows that agree on the actual residual image also
agree on every individual unknown residual represented in that image. -/
theorem residual_row_payment {n : ℕ} {κ : Type*} [Fintype κ]
    (B : Matrix (Fin n) κ K) (u v : Fin n → K) (h : u ᵥ* B = v ᵥ* B)
    {z : Fin n → K} (hz : ∃ y, z = B *ᵥ y) : u ⬝ᵥ z = v ⬝ᵥ z := by
  obtain ⟨y,rfl⟩ := hz
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,h]

#print axioms paid_append_pure
#print axioms residual_row_payment
end RKResearch.Certified.TwoDonorDense
