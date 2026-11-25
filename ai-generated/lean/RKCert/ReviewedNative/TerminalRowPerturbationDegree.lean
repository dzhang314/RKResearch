module

public import RKResearch.OrderConditions
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The exact degree budget for a terminal RK row perturbation

Only the constants supplied by the unchanged donor tableau and the explicit
self-diagonal enter this scalar recursion. The stage-column specialization is
in `TerminalRowSymmetricSplit`. The theorem uses the reviewed rooted trees and
needs neither characteristic zero nor a nonzero diagonal. -/
namespace RKResearch.Certified.TerminalSplit

open RKResearch FiniteRootedTree Polynomial
open scoped FiniteRootedTree Polynomial

variable {R : Type*}

section Semiring
variable [CommSemiring R]

/-- `a` is the base donor functional on each tree, `d` its perturbation,
and `γ` is the fixed self-diagonal. `X` varies only the donor functional. -/
noncomputable def terminalRowPolynomial (a d : FiniteRootedTree → R) (γ : R) :
    FiniteRootedTree → R[X]
  | .leaf => 1
  | u ◂ v => terminalRowPolynomial a d γ u *
      (C (a v) + C γ * terminalRowPolynomial a d γ v + C (d v) * X)

@[simp] theorem eval_terminalRowPolynomial_leaf (a d : FiniteRootedTree → R)
    (γ x : R) : (terminalRowPolynomial a d γ .leaf).eval x = 1 := by
  simp [terminalRowPolynomial]

theorem eval_terminalRowPolynomial_branch (a d : FiniteRootedTree → R)
    (γ x : R) (u v : FiniteRootedTree) :
    (terminalRowPolynomial a d γ (u ◂ v)).eval x =
      (terminalRowPolynomial a d γ u).eval x *
        (a v + γ * (terminalRowPolynomial a d γ v).eval x + d v * x) := by
  simp only [terminalRowPolynomial, eval_mul, eval_add, eval_C, eval_X]

/-- Every power of `X` costs at least `r` vertices below the root.
The self term is part of the induction, not an explicit-method simplification. -/
theorem terminalRowPolynomial_degree_budget (a d : FiniteRootedTree → R)
    (γ : R) {r : ℕ} (early : ∀ t, (t.order : ℕ) < r → d t = 0)
    (t : FiniteRootedTree) :
    r * (terminalRowPolynomial a d γ t).natDegree + 1 ≤ (t.order : ℕ) := by
  induction t with
  | leaf => simp [terminalRowPolynomial]
  | butcherProduct u v ihu ihv =>
    let P := terminalRowPolynomial a d γ u
    let Q := terminalRowPolynomial a d γ v
    let G : R[X] := C (a v) + C γ * Q
    let J : R[X] := C (d v) * X
    have hg : G.natDegree ≤ Q.natDegree := by
      apply natDegree_add_le_of_degree_le
      · simp
      · exact natDegree_C_mul_le _ _
    have hg' : r * G.natDegree ≤ (v.order : ℕ) :=
      (Nat.mul_le_mul_left r hg).trans (Nat.le_of_succ_le ihv)
    have hj : r * J.natDegree ≤ (v.order : ℕ) := by
      by_cases h : (v.order : ℕ) < r
      · simp [J, early v h]
      · have hj1 : J.natDegree ≤ 1 :=
          (natDegree_C_mul_le _ _).trans natDegree_X_le
        have hm := Nat.mul_le_mul_left r hj1
        rw [Nat.mul_one] at hm
        exact hm.trans (Nat.le_of_not_gt h)
    have hf : r * (G + J).natDegree ≤ (v.order : ℕ) := by
      refine (Nat.mul_le_mul_left r (natDegree_add_le G J)).trans ?_
      rcases le_total G.natDegree J.natDegree with h | h
      · simpa only [max_eq_right h] using hj
      · simpa only [max_eq_left h] using hg'
    have hprod : r * (P * (G + J)).natDegree ≤
        r * P.natDegree + r * (G + J).natDegree := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left r natDegree_mul_le
    change r * P.natDegree + 1 ≤ (u.order : ℕ) at ihu
    change r * (P * (G + J)).natDegree + 1 ≤ ((u ◂ v).order : ℕ)
    simp only [order, PNat.add_coe]
    omega

/-- No actual varied stage weight can occur by order `r` itself. -/
theorem eval_terminalRowPolynomial_eq_zero_param (a d : FiniteRootedTree → R)
    (γ : R) {r : ℕ} (early : ∀ t, (t.order : ℕ) < r → d t = 0)
    (t : FiniteRootedTree) (pay : (t.order : ℕ) ≤ r) (x : R) :
    (terminalRowPolynomial a d γ t).eval x = (terminalRowPolynomial a d γ t).eval 0 := by
  have h := terminalRowPolynomial_degree_budget a d γ early t
  have hz : (terminalRowPolynomial a d γ t).natDegree = 0 := by
    by_contra hn
    have hm := Nat.mul_le_mul_left r
      (show 1 ≤ (terminalRowPolynomial a d γ t).natDegree by omega)
    rw [Nat.mul_one] at hm
    omega
  rw [eq_C_of_natDegree_eq_zero hz] <;> simp

/-- Two variation tokens cannot appear by order `2*r`. -/
theorem terminalRowPolynomial_natDegree_le_one (a d : FiniteRootedTree → R)
    (γ : R) {r : ℕ} (early : ∀ t, (t.order : ℕ) < r → d t = 0)
    (t : FiniteRootedTree) (pay : (t.order : ℕ) ≤ 2 * r) :
    (terminalRowPolynomial a d γ t).natDegree ≤ 1 := by
  have h := terminalRowPolynomial_degree_budget a d γ early t
  by_contra hn
  have hm := Nat.mul_le_mul_left r
    (show 2 ≤ (terminalRowPolynomial a d γ t).natDegree by omega)
  rw [Nat.mul_comm r 2] at hm
  omega

end Semiring

section Ring
variable [CommRing R]

/-- No cancellability of `2` is needed: the identity is denominator-free. -/
theorem eval_terminalRowPolynomial_symm (a d : FiniteRootedTree → R)
    (γ : R) {r : ℕ} (early : ∀ t, (t.order : ℕ) < r → d t = 0)
    (t : FiniteRootedTree) (pay : (t.order : ℕ) ≤ 2 * r) (x : R) :
    (terminalRowPolynomial a d γ t).eval x +
      (terminalRowPolynomial a d γ t).eval (-x) =
    (terminalRowPolynomial a d γ t).eval 0 + (terminalRowPolynomial a d γ t).eval 0 := by
  obtain ⟨a₁,a₀,he⟩ := exists_eq_X_add_C_of_natDegree_le_one
    (terminalRowPolynomial_natDegree_le_one a d γ early t pay)
  rw [he]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  ring

/-- At the first possible nonlinear grade, an explicit two-child tree
registers precisely the product of its two minimal donor responses. -/
theorem eval_terminalRowPolynomial_two_minimal_branches (a d : FiniteRootedTree → R)
    (γ : R) {r : ℕ} (early : ∀ t, (t.order : ℕ) < r → d t = 0)
    (u v : FiniteRootedTree) (hu : (u.order : ℕ) ≤ r) (hv : (v.order : ℕ) ≤ r)
    (x : R) :
    let P := terminalRowPolynomial a d γ ((.leaf ◂ u) ◂ v)
    P.eval x + P.eval (-x) = P.eval 0 + P.eval 0 + (2 : R) * x^2 * d u * d v := by
  dsimp only
  simp only [eval_terminalRowPolynomial_branch, eval_terminalRowPolynomial_leaf,
    eval_terminalRowPolynomial_eq_zero_param a d γ early u hu x,
    eval_terminalRowPolynomial_eq_zero_param a d γ early u hu (-x),
    eval_terminalRowPolynomial_eq_zero_param a d γ early v hv x,
    eval_terminalRowPolynomial_eq_zero_param a d γ early v hv (-x)]
  ring

end Ring
end RKResearch.Certified.TerminalSplit
