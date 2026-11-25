module

public import RKCert.ReviewedNative.TerminalRowPerturbationDegree
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Symmetric terminal splitting on the reviewed native tableau

The new stages have no arrows to the original recipients and no inter-clone
entries; their self-diagonals are retained. The input contrast is tested on
actual prefix `Φ` columns. No RK existence bound is claimed. -/
namespace RKResearch.Certified.TerminalSplit

open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree BigOperators

variable {ι σ R : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]

section Semiring
variable [CommSemiring R]

/-- Append independently self-implicit terminal rows. All old stages remain
literal, and terminal parameter `x` changes only the lower-left block. -/
def terminalRows (A : Matrix ι ι R) (a d : σ → ι → R) (γ x : σ → R) :
    Matrix (ι ⊕ σ) (ι ⊕ σ) R :=
  Matrix.fromBlocks A 0 (Matrix.of fun k => a k + x k • d k) (Matrix.diagonal γ)

private theorem terminalRows_mulVec_inl (A : Matrix ι ι R) (a d : σ → ι → R)
    (γ x : σ → R) (z : ι ⊕ σ → R) (i : ι) :
    (terminalRows A a d γ x *ᵥ z) (Sum.inl i) = (A *ᵥ (z ∘ Sum.inl)) i := by
  rw [terminalRows, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inl, Matrix.zero_mulVec, add_zero]

private theorem terminalRows_mulVec_inr (A : Matrix ι ι R) (a d : σ → ι → R)
    (γ x : σ → R) (z : ι ⊕ σ → R) (k : σ) :
    (terminalRows A a d γ x *ᵥ z) (Sum.inr k) =
      a k ⬝ᵥ (z ∘ Sum.inl) + x k * (d k ⬝ᵥ (z ∘ Sum.inl)) + γ k * z (Sum.inr k) := by
  rw [terminalRows, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inr, Pi.add_apply, Matrix.mulVec_diagonal, Function.comp_apply]
  change (a k + x k • d k) ⬝ᵥ (z ∘ Sum.inl) + γ k * z (Sum.inr k) = _
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul]

/-- Every original stage column survives a zero upper-right block, at all orders. -/
theorem Φ_terminalRows_inl (A : Matrix ι ι R) (a d : σ → ι → R)
    (γ x : σ → R) (t : FiniteRootedTree) (i : ι) :
    Φ t (terminalRows A a d γ x) (Sum.inl i) = Φ t A i := by
  induction t generalizing i with
  | leaf => rfl
  | butcherProduct u v ihu ihv =>
    have hv : Φ v (terminalRows A a d γ x) ∘ Sum.inl = Φ v A := funext ihv
    simp only [Φ, Pi.mul_apply, terminalRows_mulVec_inl, ihu, hv]

/-- At each appended coordinate the polynomial is the actual rooted stage weight. -/
theorem Φ_terminalRows_inr (A : Matrix ι ι R) (a d : σ → ι → R)
    (γ x : σ → R) (t : FiniteRootedTree) (k : σ) :
    Φ t (terminalRows A a d γ x) (Sum.inr k) =
      (terminalRowPolynomial (fun u => a k ⬝ᵥ Φ u A)
        (fun u => d k ⬝ᵥ Φ u A) (γ k) t).eval (x k) := by
  induction t with
  | leaf => simp [Φ]
  | butcherProduct u v ihu ihv =>
    have hv : Φ v (terminalRows A a d γ x) ∘ Sum.inl = Φ v A :=
      funext (Φ_terminalRows_inl A a d γ x v)
    simp only [Φ, Pi.mul_apply, terminalRows_mulVec_inr, hv, ihu, ihv,
      eval_terminalRowPolynomial_branch]
    ac_rfl

theorem dotProduct_Φ_terminalRows (A : Matrix ι ι R) (a d : σ → ι → R)
    (γ x : σ → R) (b : ι → R) (w : σ → R) (t : FiniteRootedTree) :
    (Sum.elim b w) ⬝ᵥ Φ t (terminalRows A a d γ x) =
      b ⬝ᵥ Φ t A + ∑ k : σ, w k *
        (terminalRowPolynomial (fun u => a k ⬝ᵥ Φ u A)
          (fun u => d k ⬝ᵥ Φ u A) (γ k) t).eval (x k) := by
  have hleft : Φ t (terminalRows A a d γ x) ∘ Sum.inl = Φ t A :=
    funext (Φ_terminalRows_inl A a d γ x t)
  rw [Matrix.dotProduct_block, hleft]
  change b ⬝ᵥ Φ t A + (∑ k : σ, w k * Φ t (terminalRows A a d γ x) (Sum.inr k)) = _
  simp only [Φ_terminalRows_inr]

/-- At parameter zero the declared contrast has no effect on the singleton row. -/
abbrev terminalAtZero (A : Matrix ι ι R) (a d : ι → R) (γ : R) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  terminalRows A (fun _ => a) (fun _ => d) (fun _ => γ) (fun _ => 0)

end Semiring

section Ring
variable [CommRing R]

/-- Two independent terminal rows with unchanged self-diagonal and opposite
original donor perturbations. `true` is the plus row. -/
abbrev symmetricTerminalPair (A : Matrix ι ι R) (a d : ι → R) (γ x : R) :
    Matrix (ι ⊕ Bool) (ι ⊕ Bool) R :=
  terminalRows A (fun _ => a) (fun _ => d) (fun _ => γ) (fun k => cond k x (-x))

/-- The output of the two rows weighted by `w` each is exactly the old
terminal output weighted by `w+w` through the earned grade. -/
theorem dotProduct_Φ_symmetricTerminalPair (A : Matrix ι ι R) (a d b : ι → R)
    (γ x w : R) {r : ℕ} (early : ∀ u, (u.order : ℕ) < r → d ⬝ᵥ Φ u A = 0)
    (t : FiniteRootedTree) (pay : (t.order : ℕ) ≤ 2*r) :
    (Sum.elim b (fun _ : Bool => w)) ⬝ᵥ Φ t (symmetricTerminalPair A a d γ x) =
      b ⬝ᵥ Φ t A + (w+w) *
        (terminalRowPolynomial (fun u => a ⬝ᵥ Φ u A)
          (fun u => d ⬝ᵥ Φ u A) γ t).eval 0 := by
  let P := terminalRowPolynomial (fun u => a ⬝ᵥ Φ u A) (fun u => d ⬝ᵥ Φ u A) γ t
  unfold symmetricTerminalPair
  rw [dotProduct_Φ_terminalRows, Fintype.sum_bool]
  change b ⬝ᵥ Φ t A + (w * P.eval x + w * P.eval (-x)) =
    b ⬝ᵥ Φ t A + (w+w) * P.eval 0
  have hP : P.eval x + P.eval (-x) = P.eval 0 + P.eval 0 :=
    eval_terminalRowPolynomial_symm _ _ _ early t pay x
  rw [← mul_add, hP]
  ring

/-- Literal `HasOrder` transport, without division by the tree factorial or 2. -/
theorem hasOrder_symmetricTerminalPair_iff (A : Matrix ι ι R) (a d b : ι → R)
    (γ x w : R) {r p : ℕ} (early : ∀ u, (u.order : ℕ) < r → d ⬝ᵥ Φ u A = 0)
    (pay : p ≤ 2*r) :
    HasOrder p (symmetricTerminalPair A a d γ x) (Sum.elim b (fun _ => w)) ↔
      HasOrder p (terminalAtZero A a d γ) (Sum.elim b (fun _ => w+w)) := by
  have h (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ p) :
      (Sum.elim b (fun _ : Bool => w)) ⬝ᵥ Φ t (symmetricTerminalPair A a d γ x) =
      (Sum.elim b (fun _ : Unit => w+w)) ⬝ᵥ Φ t (terminalAtZero A a d γ) := by
    rw [dotProduct_Φ_symmetricTerminalPair A a d b γ x w early t (ht.trans pay)]
    unfold terminalAtZero
    rw [dotProduct_Φ_terminalRows, Fintype.sum_unique]
  constructor
  · intro ho t ht
    rw [← h t ht]
    exact ho t ht
  · intro ho t ht
    rw [h t ht]
    exact ho t ht

variable [DecidableEq ι]

/-- Remove the old self tap; a clone receives it as its own self-diagonal. -/
def detachedDonorRow (A : Matrix ι ι R) (i : ι) : ι → R := A i - Pi.single i (A i i)

theorem detachedDonorRow_apply_self (A : Matrix ι ι R) (i : ι) :
    detachedDonorRow A i i = 0 := by simp [detachedDonorRow]

/-- A parameter-zero appended copy matches any original receiver at every tree,
even when the receiver is not the last original stage. -/
theorem eval_detachedDonorRow_terminal_zero (A : Matrix ι ι R) (i : ι) (d : ι → R)
    (t : FiniteRootedTree) :
    (terminalRowPolynomial (fun u => detachedDonorRow A i ⬝ᵥ Φ u A)
      (fun u => d ⬝ᵥ Φ u A) (A i i) t).eval 0 = Φ t A i := by
  induction t with
  | leaf => simp
  | butcherProduct u v ihu ihv =>
    rw [eval_terminalRowPolynomial_branch, ihu, ihv]
    simp only [Φ, Pi.mul_apply, mul_zero, add_zero, detachedDonorRow,
      sub_dotProduct, single_dotProduct, sub_add_cancel, Matrix.mulVec_apply] <;> rfl

/-- Attach the pair without deleting the original receiver or any original
entry of `A`, and transfer any specified output mass `w+w` from it. -/
theorem hasOrder_append_symmetric_clone_iff (A : Matrix ι ι R) (d b : ι → R)
    (i : ι) (x w : R) {r p : ℕ} (early : ∀ u, (u.order : ℕ) < r → d ⬝ᵥ Φ u A = 0)
    (pay : p ≤ 2*r) :
    HasOrder p (symmetricTerminalPair A (detachedDonorRow A i) d (A i i) x)
      (Sum.elim (b - Pi.single i (w+w)) (fun _ => w)) ↔ HasOrder p A b := by
  have h (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ p) :
      (Sum.elim (b - Pi.single i (w+w)) (fun _ : Bool => w)) ⬝ᵥ
        Φ t (symmetricTerminalPair A (detachedDonorRow A i) d (A i i) x) = b ⬝ᵥ Φ t A := by
    rw [dotProduct_Φ_symmetricTerminalPair A (detachedDonorRow A i) d _ (A i i)
      x w early t (ht.trans pay), eval_detachedDonorRow_terminal_zero,
      sub_dotProduct, single_dotProduct, sub_add_cancel]
  constructor
  · intro ho t ht
    rw [← h t ht]
    exact ho t ht
  · intro ho t ht
    rw [h t ht]
    exact ho t ht

end Ring
end RKResearch.Certified.TerminalSplit
