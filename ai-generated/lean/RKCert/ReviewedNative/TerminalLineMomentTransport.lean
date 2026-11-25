module

public import RKCert.ReviewedNative.NativeTerminalTailMoments
public import RKCert.ReviewedNative.TerminalRowSymmetricSplit

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact moment transport on a single terminal observer line

The first half uses only the weighted degree budget and retains the actual
`HasOrder`. The converse uses one genuine first-order donor response at
order `r`, and tests its repeated native children. -/
namespace RKResearch.Certified.TerminalSplit

open RKResearch FiniteRootedTree Polynomial
open scoped Matrix FiniteRootedTree BigOperators Polynomial

variable {R ι σ τ : Type*} [Fintype ι] [Fintype σ] [Fintype τ]
variable [DecidableEq σ] [DecidableEq τ]

section Semiring
variable [CommSemiring R]

/-- Independent terminal rows on one affine donor line and common self-diagonal. -/
abbrev terminalLine (A : Matrix ι ι R) (a δ : ι → R) (γ : R) (x : σ → R) :
    Matrix (ι ⊕ σ) (ι ⊕ σ) R :=
  terminalRows A (fun _ => a) (fun _ => δ) (fun _ => γ) x

theorem dotProduct_Φ_terminalLine_eq_of_power_moments
    (A : Matrix ι ι R) (a δ b : ι → R) (γ : R)
    (x w : σ → R) (y v : τ → R) {r q : ℕ}
    (early : ∀ u, (u.order : ℕ) < r → δ ⬝ᵥ Φ u A = 0)
    (mom : ∀ j ≤ q, (∑ i : σ, w i * (x i)^j) = ∑ i : τ, v i * (y i)^j)
    (t : FiniteRootedTree) (pay : (t.order : ℕ) ≤ r*(q+1)) :
    Sum.elim b w ⬝ᵥ Φ t (terminalLine A a δ γ x) =
      Sum.elim b v ⬝ᵥ Φ t (terminalLine A a δ γ y) := by
  let P := terminalRowPolynomial (fun u => a ⬝ᵥ Φ u A) (fun u => δ ⬝ᵥ Φ u A) γ t
  have h : r * P.natDegree + 1 ≤ (t.order : ℕ) :=
    terminalRowPolynomial_degree_budget _ _ _ early t
  have hP : P.natDegree ≤ q := by
    by_contra hn
    have hmul := Nat.mul_le_mul_left r (show q+1 ≤ P.natDegree by omega)
    omega
  have hx := dotProduct_Φ_terminalRows A (fun _ : σ => a) (fun _ => δ) (fun _ => γ) x b w t
  have hy := dotProduct_Φ_terminalRows A (fun _ : τ => a) (fun _ => δ) (fun _ => γ) y b v t
  exact hx.trans ((congrArg (fun z => b ⬝ᵥ Φ t A + z)
    (sum_weighted_eval_eq_of_power_moments x w y v mom P hP)).trans hy.symm)

theorem hasOrder_terminalLine_iff_of_power_moments
    (A : Matrix ι ι R) (a δ b : ι → R) (γ : R)
    (x w : σ → R) (y v : τ → R) {p r q : ℕ}
    (early : ∀ u, (u.order : ℕ) < r → δ ⬝ᵥ Φ u A = 0)
    (mom : ∀ j ≤ q, (∑ i : σ, w i * (x i)^j) = ∑ i : τ, v i * (y i)^j)
    (pay : p ≤ r*(q+1)) :
    HasOrder p (terminalLine A a δ γ x) (Sum.elim b w) ↔
      HasOrder p (terminalLine A a δ γ y) (Sum.elim b v) := by
  have h (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ p) :=
    dotProduct_Φ_terminalLine_eq_of_power_moments A a δ b γ x w y v early mom t (ht.trans pay)
  constructor
  · intro ho t ht
    rw [← h t ht]
    exact ho t ht
  · intro ho t ht
    rw [h t ht]
    exact ho t ht

/-- Even for nonzero `γ`, on a minimal paid child the parameter is read
by an actual affine branch response, with no unknown implicit correction. -/
theorem terminalLine_branch_eq_affine (A : Matrix ι ι R) (a δ : ι → R)
    (γ : R) (x : σ → R) {r : ℕ}
    (early : ∀ t, (t.order : ℕ) < r → δ ⬝ᵥ Φ t A = 0)
    (u : FiniteRootedTree) (hu : (u.order : ℕ) ≤ r) (i : σ) :
    (terminalLine A a δ γ x *ᵥ Φ u (terminalLine A a δ γ x)) (Sum.inr i) =
      a ⬝ᵥ Φ u A + γ * (terminalRowPolynomial (fun t => a ⬝ᵥ Φ t A)
        (fun t => δ ⬝ᵥ Φ t A) γ u).eval 0 + (δ ⬝ᵥ Φ u A) * x i := by
  calc
    _ = Φ (.leaf ◂ u) (terminalLine A a δ γ x) (Sum.inr i) := by simp [Φ]
    _ = _ := by
      unfold terminalLine
      rw [Φ_terminalRows_inr, eval_terminalRowPolynomial_branch,
        eval_terminalRowPolynomial_leaf, one_mul,
        eval_terminalRowPolynomial_eq_zero_param _ _ _ early u hu (x i)]

end Semiring

section Field
variable [Field R]

/-- A genuine minimal donor response makes the raw parameter moments necessary.
Its affine inverse is applied to the actual paid branch-response moments. -/
theorem power_moments_eq_of_hasOrder_terminalLine
    (A : Matrix ι ι R) (a δ b : ι → R) (γ : R)
    (x w : σ → R) (y v : τ → R) {p r q : ℕ}
    (early : ∀ t, (t.order : ℕ) < r → δ ⬝ᵥ Φ t A = 0)
    (u : FiniteRootedTree) (hu : (u.order : ℕ) = r) (slope : δ ⬝ᵥ Φ u A ≠ 0)
    (pay : 1+q*r ≤ p)
    (h₀ : HasOrder p (terminalLine A a δ γ x) (Sum.elim b w))
    (h₁ : HasOrder p (terminalLine A a δ γ y) (Sum.elim b v)) :
    ∀ j ≤ q, (∑ i : σ, w i * (x i)^j) = ∑ i : τ, v i * (y i)^j := by
  let C₀ : Matrix σ ι R := Matrix.of (fun i => a + x i • δ)
  let C₁ : Matrix τ ι R := Matrix.of (fun i => a + y i • δ)
  let D₀ : Matrix σ σ R := Matrix.diagonal (fun _ => γ)
  let D₁ : Matrix τ τ R := Matrix.diagonal (fun _ => γ)
  let x' := tailBranchResponse A C₀ D₀ u
  let y' := tailBranchResponse A C₁ D₁ u
  let e := δ ⬝ᵥ Φ u A
  let c := a ⬝ᵥ Φ u A + γ * (terminalRowPolynomial (fun t => a ⬝ᵥ Φ t A)
    (fun t => δ ⬝ᵥ Φ t A) γ u).eval 0
  have hx (i : σ) : x' i = c + e*x i :=
    terminalLine_branch_eq_affine A a δ γ x early u hu.le i
  have hy (i : τ) : y' i = c + e*y i :=
    terminalLine_branch_eq_affine A a δ γ y early u hu.le i
  have hpay (j : ℕ) (hj : j ≤ q) : 1+j*(u.order : ℕ) ≤ p := by
    rw [hu]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right r hj) 1).trans pay
  have hmom (j : ℕ) (hj : j ≤ q) :
      (∑ i : σ, w i * (x' i)^j) = ∑ i : τ, v i * (y' i)^j :=
    tailBranchResponse_moment_eq_of_hasOrder A b C₀ D₀ w C₁ D₁ v h₀ h₁ u j (hpay j hj)
  let P : R[X] := C e⁻¹ * (X - C c)
  have hP : P.natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _)
  have hp (z : R) : P.eval (c+e*z) = z := by
    simp only [P, eval_mul, eval_C, eval_sub, eval_X]
    have he : c+e*z-c = e*z := by ring
    rw [he, ← mul_assoc, inv_mul_cancel₀ (show e ≠ 0 from slope), one_mul]
  intro j hj
  have hpow : (P^j).natDegree ≤ j := by
    simpa only [Nat.mul_one] using natDegree_pow_le_of_le j hP
  have he := sum_weighted_eval_eq_of_power_moments x' w y' v hmom (P^j) (hpow.trans hj)
  simpa only [eval_pow, hx, hy, hp] using he

/-- With one valid reference line, native order on a replacement line is
exactly its first `q+1` raw moments when `q = floor((p−1)/r)`. The two
integer inequalities express that exact cutoff without division. -/
theorem hasOrder_terminalLine_iff_power_moments
    (A : Matrix ι ι R) (a δ b : ι → R) (γ : R)
    (x w : σ → R) (y v : τ → R) {p r q : ℕ}
    (early : ∀ t, (t.order : ℕ) < r → δ ⬝ᵥ Φ t A = 0)
    (u : FiniteRootedTree) (hu : (u.order : ℕ) = r) (slope : δ ⬝ᵥ Φ u A ≠ 0)
    (low : 1+q*r ≤ p) (high : p ≤ r*(q+1))
    (h₀ : HasOrder p (terminalLine A a δ γ x) (Sum.elim b w)) :
    HasOrder p (terminalLine A a δ γ y) (Sum.elim b v) ↔
      ∀ j ≤ q, (∑ i : σ, w i * (x i)^j) = ∑ i : τ, v i * (y i)^j := by
  constructor
  · intro h₁
    exact power_moments_eq_of_hasOrder_terminalLine A a δ b γ x w y v early u hu slope low h₀ h₁
  · intro mom
    exact (hasOrder_terminalLine_iff_of_power_moments A a δ b γ x w y v early mom high).mp h₀

end Field
end RKResearch.Certified.TerminalSplit
