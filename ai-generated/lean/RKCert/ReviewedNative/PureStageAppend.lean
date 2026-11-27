module

public import RKCert.ReviewedNative.TwoDonorDense

@[expose] public section

/-!
# A verified chronological pure receiver from a dense decoder

A fresh stage is appended at the end of an existing tableau. Its
strict feed applies the polynomial functional `J-γ Id` to the old
decoded derivative. Its own diagonal coefficient supplies the
remaining `γ` contribution. This is a non-implicit induction on
the size of the reviewed rooted tree, not a numerical stage-order test.
-/

namespace RKResearch.Certified.TwoDonorDense

open FiniteRootedTree
open scoped Matrix FiniteRootedTree BigOperators

section Extension

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- Block extension by one physical row, with no change to old dependencies. -/
def appendStage (A : Matrix ι ι R) (v : ι → R) (γ : R) : Matrix (ι ⊕ PUnit) (ι ⊕ PUnit) R :=
  Matrix.fromBlocks A 0 (fun (_ : PUnit) => v) (fun _ _ => γ)

theorem append_mulVec_old (A : Matrix ι ι R) (v : ι → R) (γ : R) (z : ι ⊕ PUnit → R) :
    (appendStage A v γ *ᵥ z) ∘ Sum.inl = A *ᵥ (z ∘ Sum.inl) := by
  funext i
  simp [appendStage, Matrix.fromBlocks, Matrix.of_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem append_mulVec_new (A : Matrix ι ι R) (v : ι → R) (γ : R) (z : ι ⊕ PUnit → R) :
    (appendStage A v γ *ᵥ z) (Sum.inr PUnit.unit) =
      v ⬝ᵥ (z ∘ Sum.inl) + γ * z (Sum.inr PUnit.unit) := by
  simp [appendStage, Matrix.fromBlocks, Matrix.of_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_apply]

theorem append_phi_old (A : Matrix ι ι R) (v : ι → R) (γ : R) (t : FiniteRootedTree) :
    (Φ t (appendStage A v γ)) ∘ Sum.inl = Φ t A := by
  induction t with
  | leaf => rfl
  | butcherProduct t u ht hu =>
    funext i
    change Φ t (appendStage A v γ) (Sum.inl i) *
        (appendStage A v γ *ᵥ Φ u (appendStage A v γ)) (Sum.inl i) =
      Φ t A i * (A *ᵥ Φ u A) i
    rw [show Φ t (appendStage A v γ) (Sum.inl i) = (Φ t (appendStage A v γ) ∘ Sum.inl) i by rfl,
      ht, show (appendStage A v γ *ᵥ Φ u (appendStage A v γ)) (Sum.inl i) =
        ((appendStage A v γ *ᵥ Φ u (appendStage A v γ)) ∘ Sum.inl) i by rfl,
      append_mulVec_old, hu]

theorem append_normalized_old
    (A : Matrix ι ι R) (v : ι → R) (γ : R) (t : FiniteRootedTree) :
    (normalized (appendStage A v γ) t) ∘ Sum.inl = normalized A t := by
  funext i
  change (t.forestFactorial : R) * Φ t (appendStage A v γ) (Sum.inl i) =
    (t.forestFactorial : R) * Φ t A i
  exact congrArg ((t.forestFactorial : R) * ·) (congrFun (append_phi_old A v γ t) i)

theorem append_clock_old (A : Matrix ι ι R) (v : ι → R) (γ : R) (i : ι) :
    clocks (appendStage A v γ) (Sum.inl i) = clocks A i :=
  congrFun (append_mulVec_old A v γ 1) i

theorem PureAt.append_old {A : Matrix ι ι R} {i : ι} {q : ℕ}
    (h : PureAt A i q) (v : ι → R) (γ : R) :
    PureAt (appendStage A v γ) (Sum.inl i) q := by
  intro t ht
  rw [append_clock_old]
  change ((normalized (appendStage A v γ) t) ∘ Sum.inl) i = _
  rw [append_normalized_old, h t ht]

end Extension

section Decode
variable {ι K : Type*} [Fintype ι] [Field K] [CharZero K] {q : ℕ}

/-- The polynomial functional `J-γ Id` at one clock,
represented on the monomial coefficient vector. -/
def jet (x γ : K) : Fin (q+1) → K :=
  fun k => x^(k.val+1) / ((k.val+1 : ℕ) : K) - γ * x^k.val

/-- The strict predecessor row of a new pure stage, given an old decoder. -/
def pureFeed (D : Matrix (Fin (q+1)) ι K) (x γ : K) : ι → K :=
  jet x γ ᵥ* D

theorem pureFeed_eval {A : Matrix ι ι K} {D : Matrix (Fin (q+1)) ι K}
    (hD : IsDecoder A q D) (x γ : K) (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ q+1) :
    pureFeed D x γ ⬝ᵥ normalized A t =
      x^(t.order : ℕ) / (t.order : K) - γ*x^((t.order : ℕ)-1) := by
  rw [pureFeed, ← Matrix.dotProduct_mulVec, hD t ht, dotProduct_single, mul_one]
  have hk : (t.order : ℕ)-1+1 = (t.order : ℕ) := by have := t.order.pos; omega
  simp only [jet, hk]

theorem pureFeed_clock {A : Matrix ι ι K} {D : Matrix (Fin (q+1)) ι K}
    (hD : IsDecoder A q D) (x γ : K) :
    clocks (appendStage A (pureFeed D x γ) γ) (Sum.inr PUnit.unit) = x := by
  unfold clocks
  rw [append_mulVec_new]
  change pureFeed D x γ ⬝ᵥ (1 : ι → K) + γ*1 = x
  rw [← normalized_leaf A, pureFeed_eval hD x γ leaf (by simp [order])]
  simp [order]

/-- For every actual reviewed tree through size `q+2`, the appended
physical row has the exact monomial at `x`. -/
theorem pureFeed_profile {A : Matrix ι ι K} {D : Matrix (Fin (q+1)) ι K}
    (hD : IsDecoder A q D) (x γ : K) (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ q+2) :
    normalized (appendStage A (pureFeed D x γ) γ) t (Sum.inr PUnit.unit) =
      x^((t.order : ℕ)-1) := by
  induction t with
  | leaf => simp [normalized_leaf, order]
  | butcherProduct t u ihT ihU =>
    have hpT := t.order.pos
    have hpU := u.order.pos
    have hs : ((t ◂ u).order : ℕ) = (t.order : ℕ)+(u.order : ℕ) := rfl
    have hT : (t.order : ℕ) ≤ q+2 := by omega
    have hU : (u.order : ℕ) ≤ q+1 := by omega
    have hexp : ((t ◂ u).order : ℕ)-1 = ((t.order : ℕ)-1)+(u.order : ℕ) := by omega
    have hne : (u.order : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcancel : (u.order : K) * (x^(u.order : ℕ)/(u.order : K)) = x^(u.order : ℕ) := by
      rw [mul_comm, div_mul_cancel₀ _ hne]
    rw [normalized_join]
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [ihT hT, append_mulVec_new, append_normalized_old, pureFeed_eval hD x γ u hU,
      ihU (by omega), sub_add_cancel, hcancel, hexp, pow_add]

/-- The decoder-based construction buys a genuine fresh physical size-`q+2` sample. -/
theorem pureFeed_pure {A : Matrix ι ι K} {D : Matrix (Fin (q+1)) ι K}
    (hD : IsDecoder A q D) (x γ : K) :
    PureAt (appendStage A (pureFeed D x γ) γ) (Sum.inr PUnit.unit) (q+2) := by
  intro t ht
  rw [pureFeed_clock hD x γ]
  exact pureFeed_profile hD x γ t ht

end Decode

#print axioms pureFeed_pure
end RKResearch.Certified.TwoDonorDense
