module

public import RKCert.ReviewedNative.CubicEndAlgebra
public import RKCert.ReviewedNative.PolynomialDoubleAnchorMean

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.CubicEnd

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.AnchorMean
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The reflection appropriate to an actually monic cubic. -/
def reflectCubic (q : K[X]) : K[X] := -(q.comp (1-X))

private def cubic (b c e : K) : K[X] :=
  monomial 3 1 + monomial 2 b + monomial 1 c + monomial 0 e

private def quadratic (S P : K) : K[X] :=
  monomial 2 1 + monomial 1 (-S) + monomial 0 P

private theorem cubic_shape {q : K[X]} (mq : q.Monic) (qd : q.natDegree = 3) :
    q = cubic (q.coeff 2) (q.coeff 1) (q.coeff 0) := by
  calc
    q = X^3 + ∑ i ∈ Finset.range 3, C (q.coeff i)*X^i := by
      simpa only [qd] using mq.as_sum
    _ = _ := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cubic,
        ← C_mul_X_pow_eq_monomial, C_1, one_mul]
      ring

private theorem quadratic_shape {H : K[X]} (m : H.Monic) (d : H.natDegree = 2) :
    H = quadratic (-H.coeff 1) (H.coeff 0) := by
  calc
    H = X^2 + ∑ i ∈ Finset.range 2, C (H.coeff i)*X^i := by
      simpa only [d] using m.as_sum
    _ = _ := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, quadratic,
        neg_neg, ← C_mul_X_pow_eq_monomial, C_1, one_mul]
      ring

private theorem reflect_cubic (b c e : K) :
    reflectCubic (cubic b c e) = cubic (-3-b) (3+2*b+c) (-1-b-c-e) := by
  simp only [reflectCubic, cubic, add_comp, monomial_comp]
  simp only [← C_mul_X_pow_eq_monomial, C_1, C_ofNat, C_sub, C_add, C_neg, C_mul,
    pow_zero, pow_one, one_mul, mul_one]
  ring

private def atPrimitive (x : K) : K[X] →ₗ[K] K :=
  (Polynomial.leval x).comp formalPrimitiveLinear

private theorem atPrimitive_monomial (x : K) (i : ℕ) (a : K) :
    atPrimitive x (monomial i a) = (a/((i+1 : ℕ) : K))*x^(i+1) := by
  change (formalPrimitive (monomial i a)).eval x = _
  by_cases zero : a = 0
  · simp [zero, formalPrimitive]
  · simp [formalPrimitive, support_monomial i zero, eval_monomial]

/-- Extract the actual linear and constant coefficients from the two
literal end moments, without dividing an inequality by an endpoint. -/
private theorem coefficients_of_pair {u b c e : K} (un : u ≠ 0)
    (first : (formalPrimitive (X * cubic b c e)).eval u = 0)
    (second : (formalPrimitive (X^2 * cubic b c e)).eval u = 0) :
    c = -((6 : K)/5)*(u^2+b*u) ∧ e = ((2 : K)/5)*u^3+((3 : K)/10)*b*u^2 := by
  have first' : atPrimitive u (X^1 * cubic b c e) = 0 := by
    rw [pow_one]
    exact first
  have second' : atPrimitive u (X^2 * cubic b c e) = 0 := second
  have a1 : u^3/5+b*u^2/4+c*u/3+e/2 = 0 := by
    have eq : u^2*(u^3/5+b*u^2/4+c*u/3+e/2) =
        atPrimitive u (X^1*cubic b c e) := by
      simp only [cubic, mul_add, map_add, X_pow_mul_monomial, atPrimitive_monomial]
      norm_num <;> ring
    exact (mul_eq_zero.mp (eq.trans first')).resolve_left (pow_ne_zero _ un)
  have a2 : u^3/6+b*u^2/5+c*u/4+e/3 = 0 := by
    have eq : u^3*(u^3/6+b*u^2/5+c*u/4+e/3) =
        atPrimitive u (X^2*cubic b c e) := by
      simp only [cubic, mul_add, map_add, X_pow_mul_monomial, atPrimitive_monomial]
      norm_num <;> ring
    exact (mul_eq_zero.mp (eq.trans second')).resolve_left (pow_ne_zero _ un)
  have mulc : u*(c+((6 : K)/5)*(u^2+b*u)) = 0 := by
    linear_combination -24*a1+36*a2
  have hc : c = -((6 : K)/5)*(u^2+b*u) := by
    have g := (mul_eq_zero.mp mulc).resolve_left un
    linarith only [g]
  refine ⟨hc, ?_⟩
  rw [hc] at a1
  linear_combination 2*a1

private theorem midpoint_formula {u b c e : K}
    (hc : c = -((6 : K)/5)*(u^2+b*u))
    (he : e = ((2 : K)/5)*u^3+((3 : K)/10)*b*u^2) :
    endF u+(b+(3 : K)/2)*endG u =
      20*((1 : K)/8+b/4+c/2+e) := by
  rw [hc, he]
  unfold endF endG
  ring

/-- Exact glue from the two end pairs to the independent scalar bound. -/
theorem end_bounds_of_monic_cubic_moments {q : K[X]} {u v : K}
    (mq : q.Monic) (qd : q.natDegree = 3) (u0 : 0 < u) (v0 : 0 < v)
    (u1 : u ≠ 1) (overlap : 1 < u+v) (orientation : 0 ≤ u-v)
    (lu1 : (formalPrimitive (X*q)).eval u = 0)
    (lu2 : (formalPrimitive (X^2*q)).eval u = 0)
    (rv1 : (formalPrimitive (X*reflectCubic q)).eval v = 0)
    (rv2 : (formalPrimitive (X^2*reflectCubic q)).eval v = 0) :
    EndBounds u v (q.coeff 2+(3 : K)/2) := by
  let b := q.coeff 2
  let c := q.coeff 1
  let e := q.coeff 0
  have shape : q = cubic b c e := cubic_shape mq qd
  have star : reflectCubic q = cubic (-3-b) (3+2*b+c) (-1-b-c-e) := by
    rw [shape, reflect_cubic]
  obtain ⟨lc, le⟩ := coefficients_of_pair (b := b) (c := c) (e := e) u0.ne'
    (by simpa only [shape] using lu1) (by simpa only [shape] using lu2)
  obtain ⟨rc, re⟩ := coefficients_of_pair
    (b := -3-b) (c := 3+2*b+c) (e := -1-b-c-e) v0.ne'
    (by simpa only [star] using rv1) (by simpa only [star] using rv2)
  have linear : (10-6*(u+v))*(b+(3 : K)/2) = (6*(u+v)-9)*(u-v) := by
    linear_combination 5*rc-5*lc
  have lp := midpoint_formula lc le
  have rp := midpoint_formula rc re
  have paired : endF u+endF v+(b+(3 : K)/2)*(endG u-endG v) = 0 := by
    unfold endF endG at lp rp ⊢
    linear_combination lp+rp
  exact end_bounds_of_reflected_coefficients u1 overlap orientation linear paired

private theorem quadratic_mean {u S P : K} (un : u ≠ 0)
    (mean : (formalPrimitive (X^2*quadratic S P)).eval u = 0) :
    P = ((3 : K)/4)*u*S-((3 : K)/5)*u^2 := by
  have eq : u^3*(u^2/5-S*u/4+P/3) = atPrimitive u (X^2*quadratic S P) := by
    simp only [quadratic, mul_add, map_add, X_pow_mul_monomial, atPrimitive_monomial]
    norm_num <;> ring
  have paid : atPrimitive u (X^2*quadratic S P) = 0 := mean
  have core := (mul_eq_zero.mp (eq.trans paid)).resolve_left (pow_ne_zero _ un)
  linear_combination 3*core

private theorem quadratic_poly (S P : K) :
    quadratic S P = X^2-C S*X+C P := by
  simp only [quadratic, ← C_mul_X_pow_eq_monomial, C_1, C_neg,
    pow_zero, pow_one, mul_one, one_mul]
  ring

private theorem quadratic_deriv (S P : K) :
    (quadratic S P).derivative = (2 : K[X])*X-C S := by
  rw [quadratic_poly]
  simp only [pow_two, map_add, map_sub, derivative_mul, derivative_X, derivative_C,
    one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero]
  ring

private theorem anchor_deriv (u : K) :
    (anchorPair u).derivative = (2 : K[X])*X-C u := by
  simp only [anchorPair, derivative_mul, map_sub, derivative_X, derivative_C,
    sub_zero, one_mul, mul_one]
  ring

private theorem second_reconstruction_coeff (u S P : K) :
    (2*(anchorPair u).derivative*quadratic S P +
      anchorPair u*(quadratic S P).derivative).coeff 2 = -(5*S+4*u) := by
  have eq : 2*(anchorPair u).derivative*quadratic S P +
        anchorPair u*(quadratic S P).derivative =
      monomial 3 (6 : K) + monomial 2 (-(5*S+4*u)) +
        monomial 1 (4*P+3*u*S) + monomial 0 (-(2*u*P)) := by
    rw [anchor_deriv, quadratic_deriv, quadratic_poly]
    simp only [anchorPair, ← C_mul_X_pow_eq_monomial, C_ofNat, C_add, C_neg, C_mul,
      pow_zero, pow_one, mul_one, one_mul]
    ring
  simp [eq, coeff_monomial]

/-- The anchored cubic cutoff, with the exact unchanged left primitive.
Only the two end pairs are used; there are no sign-grid hypotheses. -/
theorem positive_of_monic_cubic_end_moments {q : K[X]} {u v : K}
    (mq : q.Monic) (qd : q.natDegree = 3) (u0 : 0 < u) (v0 : 0 < v)
    (u1 : u ≠ 1) (overlap : 1 < u+v) (orientation : 0 ≤ u-v)
    (lu1 : (formalPrimitive (X*q)).eval u = 0)
    (lu2 : (formalPrimitive (X^2*q)).eval u = 0)
    (rv1 : (formalPrimitive (X*reflectCubic q)).eval v = 0)
    (rv2 : (formalPrimitive (X^2*reflectCubic q)).eval v = 0) :
    u < (11 : K)/12 ∧ v < (11 : K)/12 ∧
      ∀ x : K, (14 : K)/15 ≤ x →
        0 < q.eval x ∧ 0 < (formalPrimitive (anchorPair u*q)).eval x := by
  have endBounds := end_bounds_of_monic_cubic_moments mq qd u0 v0 u1 overlap orientation
    lu1 lu2 rv1 rv2
  obtain ⟨H, hm, hd, factor, mean⟩ := exists_monic_anchored_quotient_mean mq u0.ne' lu1 lu2
  have hd2 : H.natDegree = 2 := by omega
  have fac : formalPrimitive (anchorPair u*q) = C ((6 : K)⁻¹)*(anchorPair u^2*H) := by
    have six : ((3+3 : ℕ) : K) = (6 : K) := by norm_num
    simpa only [qd, six] using factor
  have reconstruct := reconstruct_of_anchored_primitive fac
  let S := -H.coeff 1
  let P := H.coeff 0
  have hshape : H = quadratic S P := quadratic_shape hm hd2
  have mean' : P = ((3 : K)/4)*u*S-((3 : K)/5)*u^2 :=
    quadratic_mean u0.ne' (by simpa only [hshape] using mean)
  have coeff : q.coeff 2 = -(5*S+4*u)/6 := by
    rw [reconstruct, coeff_C_mul, hshape, second_reconstruction_coeff] <;> ring
  have cap : S-((3 : K)/4)*u ≤ (9 : K)/10-((11 : K)/100)*u := by
    linarith only [endBounds.sumLower, endBounds.centerLower, coeff]
  refine ⟨endBounds.leftUpper, endBounds.rightUpper, ?_⟩
  intro x hx
  have he : H.eval x = x^2-S*x+P := by
    rw [hshape, quadratic_poly] <;> simp
  have hde : H.derivative.eval x = 2*x-S := by
    rw [hshape, quadratic_deriv] <;> simp
  have hpos : 0 < H.eval x ∧ 0 < H.derivative.eval x := by
    rw [he, hde]
    exact quadratic_positive_of_anchor_cap u0 endBounds.leftUpper mean' cap hx
  have xp : 0 < x := by linarith only [hx]
  have ux : u < x := by linarith only [endBounds.leftUpper, hx]
  have Lpos : 0 < (anchorPair u).eval x := by
    simp only [anchorPair, eval_mul, eval_sub, eval_X, eval_C]
    exact mul_pos xp (sub_pos.mpr ux)
  have Ldpos : 0 < (anchorPair u).derivative.eval x := by
    rw [anchor_deriv]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X, eval_C]
    linarith only [xp, ux]
  have sixp : 0 < (6 : K)⁻¹ := inv_pos.mpr (by norm_num)
  constructor
  · rw [reconstruct]
    simp only [eval_mul, eval_add, eval_C, eval_ofNat]
    exact mul_pos sixp (add_pos (mul_pos (mul_pos (by norm_num) Ldpos) hpos.1)
      (mul_pos Lpos hpos.2))
  · rw [fac]
    simp only [eval_mul, eval_C, eval_pow]
    exact mul_pos sixp (mul_pos (sq_pos_of_pos Lpos) hpos.1)

end
end RKCert.ReviewedNative.CubicEnd
