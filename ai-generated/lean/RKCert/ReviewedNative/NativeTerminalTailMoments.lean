module

public import RKResearch.OrderConditions
public import Mathlib.Data.Matrix.Block
public import Mathlib.Algebra.Polynomial.Eval.Degree

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Actual paid moments of the branch response on a fixed-prefix tail

Arbitrary replacement tail matrices and arbitrary replacement signs are
allowed. The prefix matrix and prefix output weights are unchanged.
-/
namespace RKResearch.Certified.TerminalSplit

open RKResearch FiniteRootedTree Polynomial
open scoped Matrix FiniteRootedTree BigOperators Polynomial

variable {R ι σ τ : Type*} [CommSemiring R] [Fintype ι] [Fintype σ] [Fintype τ]

/-- The tree whose root has `k` identical immediate children `u`. -/
def rootBranchPower (u : FiniteRootedTree) : ℕ → FiniteRootedTree
  | 0 => .leaf
  | k+1 => rootBranchPower u k ◂ u

@[simp] theorem order_rootBranchPower (u : FiniteRootedTree) (k : ℕ) :
    ((rootBranchPower u k).order : ℕ) = 1 + k * (u.order : ℕ) := by
  induction k with
  | zero => simp [rootBranchPower]
  | succ k ih =>
    simp only [rootBranchPower, order, PNat.add_coe, ih, Nat.succ_mul]
    omega

/-- This identity holds on all physical rows, including a coupled implicit tail. -/
theorem Φ_rootBranchPower (A : Matrix ι ι R) (u : FiniteRootedTree) (k : ℕ) :
    Φ (rootBranchPower u k) A = (A *ᵥ Φ u A)^k := by
  induction k with
  | zero => simp [rootBranchPower]
  | succ k ih => simp only [rootBranchPower, Φ, ih, pow_succ]

/-- Prefix entries are literal; the two lower blocks may be arbitrary. -/
abbrev terminalTailMatrix (A : Matrix ι ι R) (C₀ : Matrix σ ι R) (D₀ : Matrix σ σ R) :
    Matrix (ι ⊕ σ) (ι ⊕ σ) R := Matrix.fromBlocks A 0 C₀ D₀

private theorem terminalTailMatrix_mulVec_inl (A : Matrix ι ι R)
    (C₀ : Matrix σ ι R) (D₀ : Matrix σ σ R) (z : ι ⊕ σ → R) (i : ι) :
    (terminalTailMatrix A C₀ D₀ *ᵥ z) (Sum.inl i) = (A *ᵥ (z ∘ Sum.inl)) i := by
  unfold terminalTailMatrix
  rw [Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inl, Matrix.zero_mulVec, add_zero]

theorem Φ_terminalTailMatrix_inl (A : Matrix ι ι R) (C₀ : Matrix σ ι R)
    (D₀ : Matrix σ σ R) (t : FiniteRootedTree) (i : ι) :
    Φ t (terminalTailMatrix A C₀ D₀) (Sum.inl i) = Φ t A i := by
  induction t generalizing i with
  | leaf => rfl
  | butcherProduct u v ihu ihv =>
    have hV : Φ v (terminalTailMatrix A C₀ D₀) ∘ Sum.inl = Φ v A := funext ihv
    simp only [Φ, Pi.mul_apply, terminalTailMatrix_mulVec_inl, ihu, hV]

/-- The **actual** branch response in an arbitrary replacement tail. It is
not a surrogate abscissa or an externally postulated affine line. -/
abbrev tailBranchResponse (A : Matrix ι ι R) (C₀ : Matrix σ ι R)
    (D₀ : Matrix σ σ R) (u : FiniteRootedTree) : σ → R :=
  (terminalTailMatrix A C₀ D₀ *ᵥ Φ u (terminalTailMatrix A C₀ D₀)) ∘ Sum.inr

theorem dotProduct_Φ_rootBranchPower_terminalTail (A : Matrix ι ι R)
    (C₀ : Matrix σ ι R) (D₀ : Matrix σ σ R) (b : ι → R) (w : σ → R)
    (u : FiniteRootedTree) (k : ℕ) :
    Sum.elim b w ⬝ᵥ Φ (rootBranchPower u k) (terminalTailMatrix A C₀ D₀) =
      b ⬝ᵥ Φ (rootBranchPower u k) A + ∑ i : σ, w i * tailBranchResponse A C₀ D₀ u i ^ k := by
  have hleft : Φ (rootBranchPower u k) (terminalTailMatrix A C₀ D₀) ∘ Sum.inl =
      Φ (rootBranchPower u k) A := funext (Φ_terminalTailMatrix_inl A C₀ D₀ _)
  rw [Matrix.dotProduct_block, hleft]
  change b ⬝ᵥ Φ (rootBranchPower u k) A +
    (∑ i : σ, w i * Φ (rootBranchPower u k) (terminalTailMatrix A C₀ D₀) (Sum.inr i)) = _
  simp only [Φ_rootBranchPower, Pi.pow_apply, tailBranchResponse, Function.comp_apply]

/-- Equality on a paid native rooted tree, including over coefficient rings
with zero divisors: its density is a unit because the native product is one. -/
theorem elementaryOutput_eq_of_hasOrder {A : Matrix σ σ R} {B : Matrix τ τ R}
    {w : σ → R} {v : τ → R} {p : ℕ} (hA : HasOrder p A w) (hB : HasOrder p B v)
    (t : FiniteRootedTree) (pay : (t.order : ℕ) ≤ p) :
    w ⬝ᵥ Φ t A = v ⬝ᵥ Φ t B := by
  have h₁ := hA t pay
  have h₂ := hB t pay
  exact (IsUnit.of_mul_eq_one _ h₁).mul_left_cancel (h₁.trans h₂.symm)

/-- Native repeated-child conditions force the response moment on any fixed-prefix
replacement tail. Neither tail is assumed diagonal, explicit or uncoupled. -/
theorem tailBranchResponse_moment_eq_of_hasOrder [IsCancelAdd R]
    (A : Matrix ι ι R) (b : ι → R) (C₀ : Matrix σ ι R) (D₀ : Matrix σ σ R) (w : σ → R)
    (C₁ : Matrix τ ι R) (D₁ : Matrix τ τ R) (v : τ → R) {p : ℕ}
    (h₀ : HasOrder p (terminalTailMatrix A C₀ D₀) (Sum.elim b w))
    (h₁ : HasOrder p (terminalTailMatrix A C₁ D₁) (Sum.elim b v))
    (u : FiniteRootedTree) (k : ℕ) (pay : 1+k*(u.order : ℕ) ≤ p) :
    (∑ i : σ, w i * tailBranchResponse A C₀ D₀ u i ^ k) =
      ∑ i : τ, v i * tailBranchResponse A C₁ D₁ u i ^ k := by
  have hpay : ((rootBranchPower u k).order : ℕ) ≤ p := by
    simpa only [order_rootBranchPower] using pay
  have h := elementaryOutput_eq_of_hasOrder h₀ h₁ (rootBranchPower u k) hpay
  simp only [dotProduct_Φ_rootBranchPower_terminalTail] at h
  exact add_left_cancel h

private theorem sum_weighted_eval_by_power_moments (x w : σ → R) (P : R[X])
    {q : ℕ} (hP : P.natDegree ≤ q) :
    (∑ i : σ, w i * P.eval (x i)) =
      ∑ j ∈ Finset.range (q+1), P.coeff j * (∑ i : σ, w i * (x i)^j) := by
  simp_rw [eval_eq_sum_range' (Nat.lt_succ_iff.mpr hP), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ac_rfl

/-- Equality of bounded raw power moments is equality on every polynomial of
that degree, without an invertibility, positivity or distinctness assumption. -/
theorem sum_weighted_eval_eq_of_power_moments (x w : σ → R) (y v : τ → R)
    {q : ℕ} (mom : ∀ j ≤ q, (∑ i : σ, w i * (x i)^j) = ∑ i : τ, v i * (y i)^j)
    (P : R[X]) (hP : P.natDegree ≤ q) :
    (∑ i : σ, w i * P.eval (x i)) = ∑ i : τ, v i * P.eval (y i) := by
  rw [sum_weighted_eval_by_power_moments x w P hP, sum_weighted_eval_by_power_moments y v P hP]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mom j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]

end RKResearch.Certified.TerminalSplit
