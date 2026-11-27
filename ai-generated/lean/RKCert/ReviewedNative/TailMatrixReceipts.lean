module

public import RKCert.ReviewedNative.TwoOrderMomentTail
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! Finite matrix witnesses imply the symbolic tail hypotheses. -/

namespace RKResearch.Certified.TwoOrderMomentTail
open FiniteRootedTree TwoDonorDense
open scoped Matrix FiniteRootedTree BigOperators

section Matrices
variable {ι η K : Type*} [Fintype ι] [Fintype η] [Field K] [CharZero K]

def momentRows {α : Type*} (n : ℕ) (b c : α → K) : Matrix (Fin n) α K :=
  fun j => row b c j.val

omit [CharZero K] in
theorem momentRows_apply {α : Type*} [Fintype α] (n : ℕ) (b c x : α → K) (j : Fin n) :
    (momentRows n b c *ᵥ x) j = read b c j.val x := rfl

omit [CharZero K] in
/-- Weighted row conditions as two finite matrix multiplications. -/
theorem adjoint_rows_from_matrices {q : ℕ} {A : Matrix ι ι K} {b : ι → K}
    {U : Matrix η ι K} {B : Matrix η η K} {w c : η → K}
    (G H : Matrix (Fin q) (Fin (q+1)) K)
    (hG : momentRows q w c * B = G * momentRows (q+1) w c)
    (hH : momentRows q w c * U = H * momentRows (q+1) b (clocks A))
    (j : Fin q) (y : ι → K) (z : η → K) :
    read w c j.val (U *ᵥ y + B *ᵥ z) =
      (∑ k : Fin (q+1), G j k * read w c k.val z) +
      (∑ k : Fin (q+1), H j k * read b (clocks A) k.val y) := by
  have hh : (momentRows q w c *ᵥ (U *ᵥ y)) j =
      (H *ᵥ (momentRows (q+1) b (clocks A) *ᵥ y)) j := by
    rw [Matrix.mulVec_mulVec, hH, Matrix.mulVec_mulVec]
  have hg : (momentRows q w c *ᵥ (B *ᵥ z)) j =
      (G *ᵥ (momentRows (q+1) w c *ᵥ z)) j := by
    rw [Matrix.mulVec_mulVec, hG, Matrix.mulVec_mulVec]
  change _ = (G *ᵥ (momentRows (q+1) w c *ᵥ z)) j +
    (H *ᵥ (momentRows (q+1) b (clocks A) *ᵥ y)) j
  rw [← hg, ← hh]
  change (momentRows q w c *ᵥ (U *ᵥ y + B *ᵥ z)) j = _
  rw [Matrix.mulVec_add, Pi.add_apply, add_comm]

/-- A pure donor's strict row integrates each paid monomial less its self tap. -/
theorem pure_predecessor [DecidableEq ι] {A : Matrix ι ι K} {q : ℕ}
    (i : ι) (hp : PureAt A i (q+1)) (γ : K) (t : FiniteRootedTree)
    (ht : (t.order : ℕ) ≤ q) :
    (A i - Pi.single i γ) ⬝ᵥ normalized A t =
      clocks A i ^ (t.order : ℕ)/(t.order : K) - γ * clocks A i ^ ((t.order : ℕ)-1) := by
  have ho : ((leaf ◂ t).order : ℕ) = 1+(t.order : ℕ) := rfl
  have hh := hp (leaf ◂ t) (by omega)
  rw [normalized_join, normalized_leaf] at hh
  simp only [one_mul, Pi.smul_apply, smul_eq_mul, ho] at hh
  have hn : 1+(t.order : ℕ)-1 = (t.order : ℕ) := by omega
  rw [hn] at hh
  have hne : (t.order : K) ≠ 0 := Nat.cast_ne_zero.mpr (by have := t.order.pos; omega)
  have heq : A i ⬝ᵥ normalized A t =
      clocks A i ^ (t.order : ℕ)/(t.order : K) :=
    (eq_div_iff hne).mpr (by simpa only [Matrix.mulVec, mul_comm] using hh)
  rw [sub_dotProduct, heq, single_dotProduct, hp t (by omega)]

/-- The new times are checked from the actual row sums, not a separate
claimed clock column. For a paid feed, use just its leaf equation. -/
theorem tail_clocks_from_feed {q : ℕ} (hq : 1 ≤ q)
    {A : Matrix ι ι K} {U : Matrix η ι K} {B : Matrix η η K} {c : η → K}
    (h : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q →
      U *ᵥ normalized A t + B *ᵥ (c^((t.order : ℕ)-1)) =
      ((1 / (t.order : K)) : K) • c^(t.order : ℕ)) :
    tail (clocks (tableau A U B)) = c := by
  unfold clocks
  rw [tail_action]
  have h1 := h leaf (by simpa [order] using hq)
  simpa [head, tail, normalized_leaf, order] using h1

end Matrices

section Reindex
variable {α β R : Type*} [Fintype α] [Fintype β] [CommSemiring R]

def shifted (e : α ≃ β) (A : Matrix α α R) : Matrix β β R :=
  fun i j => A (e.symm i) (e.symm j)

theorem action_shifted (e : α ≃ β) (A : Matrix α α R) (v : α → R) :
    shifted e A *ᵥ (v ∘ e.symm) = (A *ᵥ v) ∘ e.symm := by
  funext j
  unfold shifted Matrix.mulVec dotProduct
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

theorem phi_shifted (e : α ≃ β) (A : Matrix α α R) (t : FiniteRootedTree) :
    Φ t (shifted e A) = Φ t A ∘ e.symm := by
  induction t with
  | leaf => rfl
  | butcherProduct t u ht hu =>
    simp only [Φ, ht, hu, action_shifted]
    rfl

theorem order_shifted (e : α ≃ β) (A : Matrix α α R) (b : α → R) (p : ℕ) :
    HasOrder p (shifted e A) (b ∘ e.symm) ↔ HasOrder p A b := by
  have heq (v : α → R) : (b ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = b ⬝ᵥ v := by
    unfold dotProduct
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  simp only [HasOrder, phi_shifted, heq]
end Reindex

#print axioms adjoint_rows_from_matrices
#print axioms pure_predecessor
#print axioms order_shifted
end RKResearch.Certified.TwoOrderMomentTail
