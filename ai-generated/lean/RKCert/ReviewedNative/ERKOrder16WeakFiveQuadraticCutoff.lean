module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveMoments
import RKCert.ReviewedNative.CubicJacobiPencilSix
import RKCert.ReviewedNative.UnitBubbleMoments
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.WeakFive16

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.JacobiSix RKCert.ReviewedNative.UnitBubbleMoments
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def quad (a b c : K) : K[X] :=
  monomial 0 c + monomial 1 b + monomial 2 a

private theorem quad_of_degree_le_two (q : K[X]) (d : q.natDegree ≤ 2) :
    q = quad (q.coeff 2) (q.coeff 1) (q.coeff 0) := by
  have h := q.as_sum_range' 3 (Nat.lt_succ_of_le d)
  simpa only [quad, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using h

private theorem integral_monomial_at (u : K) (i : ℕ) (a : K) :
    integral 0 u (monomial i a) = (a / (i + 1 : K)) * u^(i + 1) := by
  by_cases h : a = 0
  · simp [h, formalPrimitive]
  rw [integral_zero_left]
  simp [formalPrimitive, support_monomial i h, eval_monomial]

private theorem anchored_quadratic_coefficients {q : K[X]} (d : q.natDegree ≤ 2)
    {u : K} (un : u ≠ 0) (h1 : integral 0 u (X * q) = 0)
    (h2 : integral 0 u (X^2 * q) = 0) :
    q.coeff 1 = -(6/5) * q.coeff 2 * u ∧ q.coeff 0 = (3/10) * q.coeff 2 * u^2 := by
  let a := q.coeff 2
  let b := q.coeff 1
  let c := q.coeff 0
  have rep : q = quad a b c := quad_of_degree_le_two q d
  have p1 : integral 0 u ((X : K[X])^1 * quad a b c) = 0 := by
    rwa [← rep, pow_one]
  have p2 : integral 0 u ((X : K[X])^2 * quad a b c) = 0 := by
    rwa [← rep]
  have m1 : a*u^2/4 + b*u/3 + c/2 = 0 := by
    have e : u^2 * (a*u^2/4 + b*u/3 + c/2) =
        integral 0 u ((X : K[X])^1 * quad a b c) := by
      simp only [quad, mul_add, map_add, X_pow_mul_monomial, integral_monomial_at]
      norm_num <;> ring
    exact (mul_eq_zero.mp (e.trans p1)).resolve_left (pow_ne_zero 2 un)
  have m2 : a*u^2/5 + b*u/4 + c/3 = 0 := by
    have e : u^3 * (a*u^2/5 + b*u/4 + c/3) =
        integral 0 u ((X : K[X])^2 * quad a b c) := by
      simp only [quad, mul_add, map_add, X_pow_mul_monomial, integral_monomial_at]
      norm_num <;> ring
    exact (mul_eq_zero.mp (e.trans p2)).resolve_left (pow_ne_zero 3 un)
  have bEq : b = -(6/5)*a*u := by
    have e : u*(b+(6/5)*a*u) = 0 := by
      linear_combination (-24 : K)*m1 + (36 : K)*m2
    linarith only [(mul_eq_zero.mp e).resolve_left un]
  have cEq : c = (3/10)*a*u^2 := by
    rw [bEq] at m1
    linear_combination (2 : K)*m1
  exact ⟨bEq, cEq⟩

private theorem quad_comp_reflect (a b c : K) :
    (quad a b c).comp (1 - X) = quad a (-2*a-b) (a+b+c) := by
  simp only [quad, ← C_mul_X_pow_eq_monomial, add_comp, mul_comp, C_comp, pow_comp,
    X_comp, map_add, map_sub, map_neg, map_mul, map_ofNat, pow_zero, pow_one, mul_one]
  ring

private theorem reflect_degree : (1 - X : K[X]).natDegree = 1 := by
  have e : (1 - X : K[X]) = -(X - C (1 : K)) := by simp [neg_sub]
  rw [e, natDegree_neg, natDegree_X_sub_C]

/-- A single leading coefficient determines the paid degree d+1 line.
The difference is detected by the checked positive-square test. -/
private theorem same_paid_top_line {D J : K[X]} {d : ℕ}
    (dd : D.natDegree = d+1) (jd : J.natDegree = d+1) (jm : J.Monic)
    (od : OrthogonalThrough D d) (oj : OrthogonalThrough J d) (pay : 2*d+2 < 19) :
    D = C (D.coeff (d+1)) * J := by
  let k := D.coeff (d+1)
  let E := D - C k * J
  have jc : J.coeff (d+1) = 1 := by
    rw [← jd, coeff_natDegree]
    exact jm.leadingCoeff
  have boundJ : (C k * J).natDegree ≤ d+1 :=
    (natDegree_C_mul_le k J).trans jd.le
  have boundE : E.natDegree ≤ d+1 := by
    simpa only [E, max_self] using natDegree_sub_le_of_le dd.le boundJ
  have lowerE : E.natDegree ≤ d := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases ei : i = d+1
    · subst i
      simp only [E, coeff_sub, coeff_C_mul, jc, mul_one, k, sub_self]
    · exact coeff_eq_zero_of_natDegree_lt (boundE.trans_lt (by omega))
  have orthE : OrthogonalThrough E d := by
    intro R rd
    have expand : bubble K * E * R = bubble K * D * R - k • (bubble K * J * R) := by
      dsimp only [E]
      rw [smul_eq_C_mul]
      ring
    rw [expand, map_sub, map_smul, od R rd, oj R rd, smul_zero, sub_zero]
  exact sub_eq_zero.mp (zero_of_orthogonalThrough orthE lowerE pay)

/-- The degree-two alternative of the same actual twelve-moment packet
cannot occur. Both paid end pairs determine the value of the first
non-origin clock; the first clock then fails the checked degree-six
Jacobi line. -/
theorem Moments.natDegree_ne_two {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) : q.natDegree ≠ 2 := by
  intro deg
  let u := c 1
  let v := 1 - c 4
  let a := q.coeff 2
  let b := q.coeff 1
  let e := q.coeff 0
  have un : u ≠ 0 := M.clock_ne_zero (i := 1) (by decide)
  have vn : v ≠ 0 := sub_ne_zero.mpr (M.active 4).1.symm
  have an : a ≠ 0 := by
    change q.coeff 2 ≠ 0
    rw [← deg, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr M.qNonzero
  obtain ⟨bLeft, eLeft⟩ := anchored_quadratic_coefficients deg.le un
    M.forwardFirst M.forwardSecond
  have bEq : b = -(6/5)*a*u := bLeft
  have eEq : e = (3/10)*a*u^2 := eLeft
  let q' := q.comp (1 - X)
  have q'd : q'.natDegree ≤ 2 := by
    simpa only [q', natDegree_comp, reflect_degree, mul_one] using deg.le
  have r1 : integral 0 v (X * q') = 0 := by
    have h := integral_reflect ((1 - X) * q) (c 4)
    rw [mul_comp, sub_comp, one_comp, X_comp, sub_sub_cancel] at h
    exact h.trans M.reverseFirst
  have r2 : integral 0 v (X^2 * q') = 0 := by
    have h := integral_reflect ((1 - X)^2 * q) (c 4)
    rw [mul_comp, pow_comp, sub_comp, one_comp, X_comp, sub_sub_cancel] at h
    exact h.trans M.reverseSecond
  obtain ⟨bRight, eRight⟩ := anchored_quadratic_coefficients q'd vn r1 r2
  have comp : q' = quad a (-2*a-b) (a+b+e) := by
    change q.comp (1 - X) = _
    have rep : q = quad a b e := quad_of_degree_le_two q deg.le
    calc
      _ = (quad a b e).comp (1 - X) := congrArg (fun p : K[X] => p.comp (1 - X)) rep
      _ = _ := quad_comp_reflect a b e
  have coeff2 : q'.coeff 2 = a := by rw [comp]; simp [quad, coeff_monomial]
  have coeff1 : q'.coeff 1 = -2*a-b := by rw [comp]; simp [quad, coeff_monomial]
  have coeff0 : q'.coeff 0 = a+b+e := by rw [comp]; simp [quad, coeff_monomial]
  have first : -2*a-b = -(6/5)*a*v := by rw [← coeff1, bRight, coeff2]
  have second : a+b+e = (3/10)*a*v^2 := by rw [← coeff0, eRight, coeff2]
  rw [bEq] at first second
  rw [eEq] at second
  have sum : u+v = 5/3 := by
    have h : a*(u+v-5/3) = 0 := by linear_combination (5/6 : K)*first
    linarith only [(mul_eq_zero.mp h).resolve_left an]
  have rest : 1-(6/5)*u+(3/10)*(u^2-v^2) = 0 := by
    have h : a*(1-(6/5)*u+(3/10)*(u^2-v^2)) = 0 := by linear_combination second
    exact (mul_eq_zero.mp h).resolve_left an
  have diff : u^2-v^2 = (5/3)*(u-v) := by
    calc
      _ = (u+v)*(u-v) := by ring
      _ = _ := by rw [sum]
  rw [diff] at rest
  have pivot : u = 5/6 := by linarith only [sum, rest]
  let H := nodalTail c Z
  have hm : H.Monic := by
    change ((X-C (c 1)) * (X-C (c 4)) * Z).Monic
    rw [M.middleFactor]
    exact ((monic_X_sub_C _).mul (monic_X_sub_C _)).mul
      ((monic_X_sub_C _).mul (monic_X_sub_C _))
  have hd : H.natDegree = 4 := by
    change ((X-C (c 1)) * (X-C (c 4)) * Z).natDegree = 4
    rw [M.middleFactor, natDegree_mul ((monic_X_sub_C _).mul (monic_X_sub_C _)).ne_zero
      ((monic_X_sub_C _).mul (monic_X_sub_C _)).ne_zero,
      natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
      natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)]
    norm_num [natDegree_X_sub_C]
  let D := q * H
  have d6 : D.natDegree = 6 := by
    change (q * H).natDegree = 6
    rw [natDegree_mul M.qNonzero hm.ne_zero, deg, hd]
  have dOrth : OrthogonalThrough D 5 := by
    intro R rd
    exact M.weightedMoments R rd
  have jOrth : OrthogonalThrough (J6 K) 5 := J6_orthogonal
  have line : D = C (D.coeff 6) * J6 K :=
    same_paid_top_line (d := 5) d6 (J6_natDegree K) (J6_monic K) dOrth jOrth (by decide)
  have liveD : D.coeff 6 ≠ 0 := by
    rw [← d6, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (mul_ne_zero M.qNonzero hm.ne_zero)
  have zD : D.eval u = 0 := by simp [D, H, nodalTail, u]
  rw [line, eval_mul, eval_C, pivot] at zD
  have liveJ : (J6 K).eval (5/6 : K) ≠ 0 := by
    rw [J6_eval_centered]
    norm_num
  exact (mul_ne_zero liveD liveJ) zD

end
end RKCert.ReviewedNative.WeakFive16
