module

public import Mathlib.LinearAlgebra.Lagrange

import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # A finite, purely ordered-field replacement for pole-gap arguments

The next-to-top polynomial of a monic simple split pencil must at some
site match the sign of the pencil's derivative. This is the top coefficient
of its finite interpolation formula, not an intermediate value assertion. -/

namespace RKCert.ReviewedNative.PolynomialCertificate

open Polynomial
open scoped Polynomial BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {ι : Type*} [DecidableEq ι]

theorem root_polynomial_eq_nodal (s : Finset ι) {v : ι → K} (inj : Set.InjOn v s)
    {T : K[X]} (mono : T.Monic) (degree : T.degree = s.card) (roots : ∀ i ∈ s, T.IsRoot (v i)) :
    T = Lagrange.nodal s v := by
  apply Polynomial.eq_of_degree_le_of_eval_index_eq s inj degree.le
  · exact degree.trans Lagrange.degree_nodal.symm
  · exact mono.leadingCoeff.trans Lagrange.nodal_monic.leadingCoeff.symm
  · intro i hi
    exact (roots i hi).trans (Lagrange.eval_nodal_at_node hi).symm

theorem exists_positive_derivative_product (s : Finset ι) {v : ι → K} (inj : Set.InjOn v s)
    {T A : K[X]} (mono : T.Monic) (deg : T.degree = s.card) (roots : ∀ i ∈ s, T.IsRoot (v i))
    (low : A.degree < s.card) (top : 0 < A.coeff (s.card - 1)) :
    ∃ i ∈ s, 0 < A.eval (v i) * T.derivative.eval (v i) := by
  have nodal := root_polynomial_eq_nodal s inj mono deg roots
  by_contra! no
  have nonpos : (∑ i ∈ s, A.eval (v i) / ∏ j ∈ s.erase i, (v i - v j)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    let d := T.derivative.eval (v i)
    have deq : d = ∏ j ∈ s.erase i, (v i - v j) := by
      change T.derivative.eval (v i) = _
      rw [nodal, Lagrange.eval_nodal_derivative_eval_node_eq hi, Lagrange.eval_nodal]
    rw [← deq]
    have prodnon : A.eval (v i) * d ≤ 0 := no i hi
    by_cases hn : d = 0
    · simp [hn]
    · calc
        A.eval (v i) / d = (A.eval (v i) * d) / d ^ 2 := by field_simp <;> ring
        _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg prodnon (sq_nonneg d)
  rw [← Lagrange.coeff_eq_sum inj low] at nonpos
  exact (not_lt_of_ge nonpos) top

/-- If 3W ≥ 80 P7² throughout the sites of the degree-eight pencil, then
the pencil coefficient is strictly above -3/80. No pole roots, simplicity
of reference polynomials, or real closure of the supplied site field enter.
The numbers are parameters, so the principle applies to other pencils. -/
theorem pencil_lower_of_wronskian (s : Finset ι) {v : ι → K} (inj : Set.InjOn v s)
    (P Q : K[X]) (d κ a b : K) (a0 : 0 < a) (b0 : 0 < b)
    (mono : ((X - C d) * P - C κ * Q).Monic)
    (deg : ((X - C d) * P - C κ * Q).degree = (s.card : WithBot ℕ))
    (roots : ∀ i ∈ s, ((X - C d) * P - C κ * Q).IsRoot (v i))
    (low : P.degree < s.card) (top : 0 < P.coeff (s.card - 1))
    (wr : ∀ i ∈ s, b * (P.eval (v i)) ^ 2 ≤
      a * (Q.eval (v i) * P.derivative.eval (v i) - Q.derivative.eval (v i) * P.eval (v i))) :
    -(a / b) < κ := by
  obtain ⟨i, hi, pos⟩ := exists_positive_derivative_product s inj mono deg roots low top
  let x := v i
  let W := Q.eval x * P.derivative.eval x - Q.derivative.eval x * P.eval x
  have bound : b * P.eval x ^ 2 ≤ a * W := wr i hi
  have W0 : 0 ≤ W := by
    have ab : 0 ≤ a * W := (mul_nonneg b0.le (sq_nonneg _)).trans bound
    exact nonneg_of_mul_nonneg_right ab a0
  have rt : (x - d) * P.eval x - κ * Q.eval x = 0 := by
    simpa only [IsRoot, eval_sub, eval_mul, eval_X, eval_C, x] using roots i hi
  have deriv : P.eval x * (((X-C d) * P - C κ * Q).derivative.eval x) =
      P.eval x ^ 2 + κ * W := by
    simp only [derivative_sub, derivative_mul, derivative_X, derivative_C, sub_zero, one_mul,
      zero_mul, zero_add, eval_sub, eval_add, eval_mul, eval_X, eval_C, W]
    linear_combination (P.derivative.eval x) * rt
  change 0 < P.eval x * (((X-C d) * P - C κ * Q).derivative.eval x) at pos
  rw [deriv] at pos
  by_contra! bad
  have kb : κ * b ≤ -a := by
    apply (le_div_iff₀ b0).mp
    simpa only [neg_div] using bad
  have h := mul_le_mul_of_nonneg_right kb W0
  have h' := mul_pos b0 pos
  nlinarith only [bound, h, h']

end RKCert.ReviewedNative.PolynomialCertificate
