module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # A paid nodal moment forbids a marked separator root

A proposed cut at the mark supplies one exact polynomial cancellation.
There is no separate signed atomic quadrature or extra moment assumption. -/
namespace RKCert.ReviewedNative.FiniteOrderedSigns

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The displayed nodal hull is `(X - C c) * D`. If a separator `H` of
degree `k` had a root at `c`, the tester would have degree
`k + D.natDegree - 1` and its paid product would be `H * D^2), of
degree `k + 2 * D.natDegree`. The live sample ensures strict positivity
of exactly this unnormalized cardinal square. -/
theorem separator_eval_ne_of_paid_nodal
    {ι : Type*} (sites : Finset ι) (x weight : ι → K)
    {b : ℕ} {c : K} {H D : K[X]}
    (budget : H.natDegree + D.natDegree ≤ b + 1)
    (paid : ∀ R : K[X], R.natDegree ≤ b →
      (∑ i ∈ sites, weight i * (((X - C c) * D * R).eval (x i))) = 0)
    (fit : ∀ i ∈ sites, 0 ≤ weight i * H.eval (x i))
    (live : ∃ i ∈ sites, 0 < weight i * H.eval (x i) ∧ D.eval (x i) ≠ 0) :
    H.eval c ≠ 0 := by
  classical
  intro root
  obtain ⟨i, hi, ip, id⟩ := live
  have Hn : H ≠ 0 := by
    intro h
    have bad : (0 : K) < 0 := by
      simpa only [h, eval_zero, mul_zero] using ip
    exact (lt_irrefl _) bad
  have Dn : D ≠ 0 := by
    intro h
    exact id (by rw [h, eval_zero])
  have atMark : H.IsRoot c := root
  obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr atMark
  have Qn : Q ≠ 0 := by
    intro h
    apply Hn
    rw [hQ, h, mul_zero]
  have hd : H.natDegree = 1 + Q.natDegree := by
    rw [hQ, natDegree_mul (X_sub_C_ne_zero c) Qn, natDegree_X_sub_C]
  have cost : (Q * D).natDegree ≤ b := by
    rw [natDegree_mul Qn Dn]
    omega
  have cancel : (X - C c) * D * (Q * D) = H * D^2 := by
    rw [hQ]
    ring
  have zero := paid (Q * D) cost
  rw [cancel] at zero
  have positive : 0 < ∑ j ∈ sites, weight j * ((H * D^2).eval (x j)) := by
    apply Finset.sum_pos'
    · intro j hj
      simp only [eval_mul, eval_pow, ← mul_assoc]
      exact mul_nonneg (fit j hj) (sq_nonneg _)
    · refine ⟨i, hi, ?_⟩
      simp only [eval_mul, eval_pow, ← mul_assoc]
      exact mul_pos ip (sq_pos_of_ne_zero id)
  exact positive.ne' zero

end RKCert.ReviewedNative.FiniteOrderedSigns
