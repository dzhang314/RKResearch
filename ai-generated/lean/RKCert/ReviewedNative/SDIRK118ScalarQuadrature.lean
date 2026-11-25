module

public import RKCert.ReviewedNative.SDIRK118LiteralClaimPin
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Derivative

import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarQuadrature

open RKResearch
open RKResearch.Certified.PaidDefectBridge.SDIRK118 (PolyBound wDot)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ClaimPin (MonomialBasis standardPowers ExactScalarSeed Bstar)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.LiteralAssembly (Geometry)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarBindings
open Polynomial
open scoped Polynomial Matrix BigOperators

local notation "ℙ" => Polynomial ℝ

section Primitive

/-- The actually emitted evaluator agrees with polynomial evaluation on
every polynomial, not just a finite table of clocks. -/
theorem evalAt_eq_leval (M : MonomialBasis) (hM : standardPowers M) (x : ℝ) :
    evalAt M x = Polynomial.leval x := by
  apply M.ext
  intro n
  rw [hM n]
  change evalAt M x (X ^ n) = (X ^ n : ℙ).eval x
  rw [ScalarBindings.eval_pow M hM, Polynomial.eval_pow, eval_X]

theorem evalAt_eq_eval (M : MonomialBasis) (hM : standardPowers M)
    (x : ℝ) (P : ℙ) : evalAt M x P = P.eval x := by
  rw [evalAt_eq_leval M hM] <;> rfl

theorem derivative_primitive (M : MonomialBasis) (hM : standardPowers M) (P : ℙ) :
    derivative (coefficientPrimitive M P) = P := by
  have h : derivative.comp (coefficientPrimitive M) = LinearMap.id := by
    apply M.ext
    intro n
    rw [hM n]
    change derivative (coefficientPrimitive M (X ^ n)) = X ^ n
    have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have hc : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by simp
    rw [primitive_pow M hM, derivative_smul, derivative_X_pow_succ,
      ← smul_eq_C_mul, hc, smul_smul, inv_mul_cancel₀ hn, one_smul]
  exact congrArg (fun f : ℙ →ₗ[ℝ] ℙ => f P) h

theorem primitive_eval_zero (M : MonomialBasis) (hM : standardPowers M) (P : ℙ) :
    (coefficientPrimitive M P).eval 0 = 0 := by
  have h : (Polynomial.leval (0 : ℝ)).comp (coefficientPrimitive M) = 0 := by
    apply M.ext
    intro n
    rw [hM n]
    change (coefficientPrimitive M (X ^ n)).eval 0 = 0
    rw [primitive_pow M hM, Polynomial.eval_smul, Polynomial.eval_pow, eval_X, pow_succ,
      mul_zero, smul_zero]
  exact congrArg (fun f : ℙ →ₗ[ℝ] ℝ => f P) h

theorem primitive_degree (M : MonomialBasis) (hM : standardPowers M)
    (n : ℕ) (P : ℙ) (hP : PolyBound n P) : PolyBound (n + 1) (coefficientPrimitive M P) := by
  intro j hj
  have hidx : j - 1 + 1 = j := by omega
  have hn : (((j - 1 : ℕ) : ℝ) + 1) ≠ 0 :=
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one).ne'
  have h := congrArg (fun Q : ℙ => Q.coeff (j - 1)) (derivative_primitive M hM P)
  change (derivative (coefficientPrimitive M P)).coeff (j - 1) = P.coeff (j - 1) at h
  rw [coeff_derivative, hP (j - 1) (by omega)] at h
  have hzero := (mul_eq_zero.mp h).resolve_right hn
  rwa [hidx] at hzero

theorem mean_eq_eval_primitive (M : MonomialBasis) (hM : standardPowers M) (P : ℙ) :
    mean M P = (coefficientPrimitive M P).eval 1 := by
  exact evalAt_eq_eval M hM 1 (coefficientPrimitive M P)

/-- The exact coefficient-primitive version of the fundamental theorem.
The constant of integration is recovered at zero, not assumed. -/
theorem mean_derivative (M : MonomialBasis) (hM : standardPowers M) (P : ℙ) :
    mean M (derivative P) = P.eval 1 - P.eval 0 := by
  let Q := coefficientPrimitive M (derivative P)
  have hD : derivative (Q - P) = 0 := by
    rw [derivative_sub, derivative_primitive M hM P.derivative, sub_self]
  have hC := eq_C_of_derivative_eq_zero hD
  have e0 := congrArg (fun f : ℙ => f.eval 0) hC
  have e1 := congrArg (fun f : ℙ => f.eval 1) hC
  simp only [eval_sub, eval_C] at e0 e1
  have q0 : Q.eval 0 = 0 := primitive_eval_zero M hM _
  rw [q0] at e0
  rw [mean_eq_eval_primitive M hM]
  change Q.eval 1 = P.eval 1 - P.eval 0
  linarith only [e0,e1]

private def composeWith (Q : ℙ) : ℙ →ₗ[ℝ] ℙ where
  toFun P := P.comp Q
  map_add' P S := add_comp
  map_smul' a P := smul_comp a P Q

private def averageLM (M : MonomialBasis) (z : ℝ) : ℙ →ₗ[ℝ] ℝ :=
  z⁻¹ • ((evalAt M z).comp (coefficientPrimitive M))

private theorem averageLM_apply (M : MonomialBasis) (z : ℝ) (P : ℙ) :
    averageLM M z P = avg M z P := by
  change z⁻¹ * evalAt M z (coefficientPrimitive M P) =
    evalAt M z (coefficientPrimitive M P) / z
  rw [div_eq_mul_inv, mul_comm]

/-- Moving from the archived unscaled sites to the unit quadrature variable
is an equality of linear functionals on the standard monomial basis. -/
theorem mean_scale (M : MonomialBasis) (hM : standardPowers M) (z : ℝ) (hz : z ≠ 0) (P : ℙ) :
    mean M (P.comp (z • (X : ℙ))) = avg M z P := by
  have h : (mean M).comp (composeWith (z • (X : ℙ))) = averageLM M z := by
    apply M.ext
    intro n
    rw [hM n]
    change mean M ((X ^ n : ℙ).comp (z • X)) = averageLM M z (X ^ n)
    rw [X_pow_comp, smul_pow, map_smul, mean_pow M hM, averageLM_apply]
    unfold avg
    rw [primitive_pow M hM, map_smul, ScalarBindings.eval_pow M hM]
    change z ^ n * (((n + 1 : ℕ) : ℝ))⁻¹ =
      ((((n + 1 : ℕ) : ℝ))⁻¹ * z ^ (n + 1)) / z
    apply (eq_div_iff hz).2
    rw [pow_succ] <;> ring
  have e := congrArg (fun f : ℙ →ₗ[ℝ] ℝ => f P) h
  change mean M (P.comp (z • (X : ℙ))) = averageLM M z P at e
  rw [averageLM_apply] at e
  exact e

def reflect : ℙ := 1 - X

theorem eval_reflect (u : ℝ) : reflect.eval u = 1 - u := by
  simp [reflect, eval_sub]

theorem reflect_degree : reflect.natDegree ≤ 1 := by
  simpa only [reflect, natDegree_one, natDegree_X, max_eq_right (by decide : (0 : ℕ) ≤ 1)]
    using natDegree_sub_le (1 : ℙ) X

theorem clock_degree (n : ℕ) (P : ℙ) (hP : PolyBound n P) : PolyBound (n + 1) (reflect * P) := by
  have hp := natDegree_le_iff_coeff_eq_zero.mpr hP
  have hr := reflect_degree
  apply natDegree_le_iff_coeff_eq_zero.mp
  exact natDegree_mul_le.trans (by omega : reflect.natDegree + P.natDegree ≤ n + 1)

theorem comp_reflect_degree (n : ℕ) (P : ℙ) (hP : PolyBound n P) :
    PolyBound n (P.comp reflect) := by
  apply natDegree_le_iff_coeff_eq_zero.mp
  have hp := natDegree_le_iff_coeff_eq_zero.mpr hP
  calc
    (P.comp reflect).natDegree ≤ P.natDegree * reflect.natDegree := natDegree_comp_le
    _ ≤ n * 1 := Nat.mul_le_mul hp reflect_degree
    _ = n := Nat.mul_one _

private theorem derivative_reflect : derivative reflect = -1 := by
  rw [reflect, derivative_sub, derivative_one, derivative_X, zero_sub]

/-- Reflection preserves the normalized mean. This is purely formal
polynomial calculus, with both endpoint evaluations exact. -/
theorem mean_reflect (M : MonomialBasis) (hM : standardPowers M) (P : ℙ) :
    mean M (P.comp reflect) = mean M P := by
  let F := -((coefficientPrimitive M P).comp reflect)
  have dF : derivative F = P.comp reflect := by
    simp only [F, derivative_neg, derivative_comp, derivative_reflect,
      derivative_primitive M hM, neg_one_mul, neg_neg]
  rw [← dF, mean_derivative M hM, mean_eq_eval_primitive M hM]
  change (-((coefficientPrimitive M P).comp reflect)).eval 1 -
    (-((coefficientPrimitive M P).comp reflect)).eval 0 = _
  simp [eval_comp, eval_reflect, primitive_eval_zero M hM]

end Primitive

section SixSiteRule

private theorem card6_eq_basis (y : Fin 6 → ℝ) (i : Fin 6) :
    card6 y i = Lagrange.basis Finset.univ y i := by
  simp only [card6, Lagrange.basis, Lagrange.basisDivisor, smul_eq_C_mul,
    Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib]

/-- Rule written as a linear map for exact division and reconstruction. The
weights are not substituted by an unidentified six-vector. -/
def weightedEval (w y : Fin 6 → ℝ) : ℙ →ₗ[ℝ] ℝ where
  toFun P := ∑ i : Fin 6, w i * P.eval (y i)
  map_add' P Q := by
    simp only [eval_add, mul_add, Finset.sum_add_distrib]
  map_smul' a P := by
    simp only [Polynomial.eval_smul, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl (fun i _ => by ring)

theorem weightedEval_apply (w y : Fin 6 → ℝ) (P : ℙ) :
    weightedEval w y P = ∑ i : Fin 6, w i * P.eval (y i) := rfl

theorem rule_exact5 (M : MonomialBasis) (y : Fin 6 → ℝ) (hy : Function.Injective y)
    (P : ℙ) (hP : PolyBound 5 P) :
    weightedEval (scalarWeights M y) y P = mean M P := by
  have hd : P.degree < ((Finset.univ : Finset (Fin 6)).card : WithBot ℕ) := by
    have h0 : P.degree ≤ ((5 : ℕ) : WithBot ℕ) :=
      degree_le_of_natDegree_le (natDegree_le_iff_coeff_eq_zero.mpr hP)
    exact h0.trans_lt (by norm_num)
  have hp : P = ∑ i : Fin 6, P.eval (y i) • card6 y i := by
    simpa only [Lagrange.interpolate_apply, card6_eq_basis, smul_eq_C_mul] using
      Lagrange.eq_interpolate (f := P) (s := Finset.univ) (v := y) hy.injOn hd
  calc
    weightedEval (scalarWeights M y) y P =
        mean M (∑ i : Fin 6, P.eval (y i) • card6 y i) := by
      simp only [weightedEval_apply, scalarWeights, map_sum, map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    _ = mean M P := congrArg (mean M) hp.symm

private theorem div_nodal6 (y : Fin 6 → ℝ) (P : ℙ) (hP : PolyBound 7 P) :
    let N := Lagrange.nodal Finset.univ y
    ∃ (R : ℙ) (a b : ℝ), PolyBound 5 R ∧ P = R + a • N + b • (X * N) := by
  let N := Lagrange.nodal Finset.univ y
  have hm : N.Monic := Lagrange.nodal_monic
  have hd : N.natDegree = 6 := by simp [N]
  have hn : N ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hd
    omega
  let R := P %ₘ N
  let Q := P /ₘ N
  have hR : PolyBound 5 R := by
    apply natDegree_le_iff_coeff_eq_zero.mp
    have hh := natDegree_modByMonic_lt P hm hn
    rw [hd] at hh
    exact Nat.le_of_lt_succ hh
  have hQ : Q.natDegree ≤ 1 := by
    change (P /ₘ N).natDegree ≤ 1
    rw [natDegree_divByMonic P hm, hd]
    have h := natDegree_le_iff_coeff_eq_zero.mpr hP
    omega
  obtain ⟨b,a,he⟩ := exists_eq_X_add_C_of_natDegree_le_one hQ
  refine ⟨R,a,b,hR,?_⟩
  have e : R + N * Q = P := modByMonic_add_div P N
  rw [he] at e
  rw [← e]
  simp only [smul_eq_C_mul]
  ring

/-- The exact degree-seven canonical rule from just two nodal means. -/
theorem rule_exact7_of_nodal (M : MonomialBasis) (y : Fin 6 → ℝ)
    (hy : Function.Injective y)
    (hN : mean M (Lagrange.nodal Finset.univ y) = 0)
    (hXN : mean M (X * Lagrange.nodal Finset.univ y) = 0)
    (P : ℙ) (hP : PolyBound 7 P) :
    weightedEval (scalarWeights M y) y P = mean M P := by
  let N := Lagrange.nodal Finset.univ y
  have hn (i : Fin 6) : N.eval (y i) = 0 :=
    Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have h0 : weightedEval (scalarWeights M y) y N = 0 := by
    simp only [weightedEval_apply, hn, mul_zero, Finset.sum_const_zero]
  have h1 : weightedEval (scalarWeights M y) y (X * N) = 0 := by
    simp only [weightedEval_apply, eval_mul, hn, mul_zero, Finset.sum_const_zero]
  exact rule_eq_of_degree5_and_nodal (weightedEval (scalarWeights M y) y) (mean M) N P
    (rule_exact5 M y hy) h0 h1 hN hXN (div_nodal6 y P hP)

end SixSiteRule

section LiteralNodes

/-- The exact archived sites before division by z, in the literal order
used by geometry. Numerals here are layout/constants, not computed roots. -/
def rawNodes (M : MonomialBasis) (s t cStar : ℝ) : Fin 6 → ℝ :=
  ![1, aAt s, s, t, bStar M s t cStar, cStar]

theorem norm_nodes (M : MonomialBasis) (s t cStar : ℝ) (i : Fin 6) :
    yAt M s t cStar i = rawNodes M s t cStar i / zAt s := by
  fin_cases i <;> rfl

theorem literal_z_pos (M : MonomialBasis) (s t cStar : ℝ)
    (h : ExactScalarSeed M s t cStar) : 0 < zAt s := by
  have hs := h.sLower
  unfold zAt aAt
  linarith

theorem literal_b_neg (M : MonomialBasis) (s t cStar : ℝ)
    (h : ExactScalarSeed M s t cStar) : bStar M s t cStar < 0 := by
  have hc : 0 < cStar := (literal_z_pos M s t cStar h).trans h.cRight
  have h0 : quadraticAt M s t 0 = bStar M s t cStar * cStar := by
    simpa only [zero_sub, neg_mul_neg] using (quadratic_factors M s t cStar h.cRoot 0)
  have ht := h.quadAtZeroNeg
  rw [h0] at ht
  exact lt_of_not_ge (fun hb => (not_lt_of_ge (mul_nonneg hb hc.le)) ht)

theorem literal_nodes_injective (M : MonomialBasis) (s t cStar : ℝ)
    (h : ExactScalarSeed M s t cStar) : Function.Injective (yAt M s t cStar) := by
  have hz := literal_z_pos M s t cStar h
  have hb := literal_b_neg M s t cStar h
  have ht0 : 0 < t := by have h0 := h.tLower; linarith
  have hts : t < s := by have h0 := h.tUpper; have h1 := h.sLower; linarith
  have hsa : s < aAt s := by have hs := h.sUpper; unfold aAt; linarith
  have ha1 : aAt s < 1 := by have hs := h.sUpper; unfold aAt; linarith
  have h1z : 1 < zAt s := by have hs := h.sLower; unfold zAt aAt; linarith
  have hzc := h.cRight
  have hraw : Function.Injective (rawNodes M s t cStar) := by
    intro i j e
    fin_cases i <;> fin_cases j <;> simp [rawNodes] at e ⊢ <;> linarith
  intro i j e
  simp only [norm_nodes] at e
  apply hraw
  exact (div_left_inj₀ hz.ne').mp e

/-- The monic raw nodal polynomial really is the recorded quartic times
the quadratic selected by the two scalar moment equations. -/
theorem raw_nodal_factor (M : MonomialBasis) (s t cStar : ℝ)
    (hc : quadraticAt M s t cStar = 0) :
    Lagrange.nodal Finset.univ (rawNodes M s t cStar) = Bstar M s t * Zpoly s t := by
  apply Polynomial.funext
  intro x
  have hB : (Bstar M s t).eval x = (x - bStar M s t cStar) * (x - cStar) := by
    simpa only [Bstar, quadraticAt, eval_add, eval_mul, Polynomial.eval_pow, eval_X, eval_C]
      using (quadratic_factors M s t cStar hc x)
  rw [Lagrange.eval_nodal, eval_mul, hB]
  simp [rawNodes, Zpoly, Jpoly, cubic, linearFactor, Fin.prod_univ_succ, eval_sub, eval_mul]
  <;> ring

private theorem raw_nodal_zeroes (M : MonomialBasis) (s t cStar : ℝ)
    (hD : momentDet M s t ≠ 0) (hc : quadraticAt M s t cStar = 0) :
    let N := Lagrange.nodal Finset.univ (rawNodes M s t cStar)
    avg M (zAt s) N = 0 ∧ avg M (zAt s) (X * N) = 0 := by
  let J := averageLM M (zAt s)
  let Z := Zpoly s t
  let A := beta0 M s t
  let B := beta1 M s t
  have em (j : ℕ) : J (X ^ j * Z) = μ M s t j :=
    averageLM_apply M (zAt s) (X ^ j * Z)
  have e0 : Bstar M s t * Z = (A • (X ^ 0 * Z)) + B • (X ^ 1 * Z) + X ^ 2 * Z := by
    simp only [A,B,Bstar,smul_eq_C_mul,pow_zero,pow_one,one_mul]
    ring
  have e1 : X * (Bstar M s t * Z) =
      (A • (X ^ 1 * Z)) + B • (X ^ 2 * Z) + X ^ 3 * Z := by
    simp only [A,B,Bstar,smul_eq_C_mul,pow_one]
    ring
  obtain ⟨g0,g1⟩ := two_nodal_moment_equations M s t hD
  dsimp only
  rw [raw_nodal_factor M s t cStar hc]
  constructor
  · change avg M (zAt s) (Bstar M s t * Z) = 0
    rw [← averageLM_apply, e0]
    change J (A • (X ^ 0 * Z) + B • (X ^ 1 * Z) + X ^ 2 * Z) = 0
    simpa only [map_add,map_smul,em,smul_eq_mul,A,B] using g0
  · change avg M (zAt s) (X * (Bstar M s t * Z)) = 0
    rw [← averageLM_apply, e1]
    change J (A • (X ^ 1 * Z) + B • (X ^ 2 * Z) + X ^ 3 * Z) = 0
    simpa only [map_add,map_smul,em,smul_eq_mul,A,B] using g1

private theorem nodal_scale (z : ℝ) (u y : Fin 6 → ℝ) (hu : ∀ i, u i = z * y i) :
    (Lagrange.nodal Finset.univ u).comp (z • (X : ℙ)) =
      z ^ 6 • Lagrange.nodal Finset.univ y := by
  have fac (i : Fin 6) : ((X - C (u i)) : ℙ).comp (z • X) = z • (X - C (y i)) := by
    rw [sub_comp, X_comp, C_comp, hu, smul_sub, smul_eq_C_mul (p := C (y i)), map_mul]
  simp only [Lagrange.nodal_eq, prod_comp, fac]
  simpa using (Finset.smul_prod (Finset.univ : Finset (Fin 6)) z
    (fun i => (X - C (y i) : ℙ))).symm

theorem literal_nodal_zeroes (M : MonomialBasis) (hM : standardPowers M)
    (s t cStar : ℝ) (h : ExactScalarSeed M s t cStar) :
    let N := Lagrange.nodal Finset.univ (yAt M s t cStar)
    mean M N = 0 ∧ mean M (X * N) = 0 := by
  let z := zAt s
  let u := rawNodes M s t cStar
  let y := yAt M s t cStar
  let Nr := Lagrange.nodal Finset.univ u
  let N := Lagrange.nodal Finset.univ y
  have hz : z ≠ 0 := (literal_z_pos M s t cStar h).ne'
  have hu (i : Fin 6) : u i = z * y i := by
    change rawNodes M s t cStar i = z * yAt M s t cStar i
    rw [norm_nodes, mul_comm z, div_mul_cancel₀ _ hz]
  have eN : Nr.comp (z • (X : ℙ)) = z ^ 6 • N := nodal_scale z u y hu
  have exN : (X * Nr).comp (z • (X : ℙ)) = z ^ 7 • (X * N) := by
    have h7 : z * z ^ 6 = z ^ 7 := (pow_succ' z 6).symm
    rw [mul_comp, X_comp, eN, smul_mul_assoc, mul_smul_comm, smul_smul, h7]
  obtain ⟨e0,e1⟩ := raw_nodal_zeroes M s t cStar h.momentPivotPos.ne' h.cRoot
  have z0 := (mean_scale M hM z hz Nr).trans e0
  have z1 := (mean_scale M hM z hz (X * Nr)).trans e1
  rw [eN, map_smul, smul_eq_mul] at z0
  rw [exN, map_smul, smul_eq_mul] at z1
  exact ⟨(mul_eq_zero.mp z0).resolve_left (pow_ne_zero 6 hz),
    (mul_eq_zero.mp z1).resolve_left (pow_ne_zero 7 hz)⟩

/-- Every polynomial of degree at most seven is integrated by the actual
literal six cardinal masses. No certificate of a solved weight vector. -/
theorem literal_rule_exact7 (M : MonomialBasis) (hM : standardPowers M)
    (s t cStar : ℝ) (h : ExactScalarSeed M s t cStar) (P : ℙ) (hP : PolyBound 7 P) :
    weightedEval (scalarWeights M (yAt M s t cStar)) (yAt M s t cStar) P = mean M P := by
  obtain ⟨e0,e1⟩ := literal_nodal_zeroes M hM s t cStar h
  exact rule_exact7_of_nodal M (yAt M s t cStar) (literal_nodes_injective M s t cStar h)
    e0 e1 P hP

end LiteralNodes

section Green

variable (M : MonomialBasis) (hM : standardPowers M) (s t cStar : ℝ)
include hM

private theorem eval_geometry_x (P : ℙ) (i : Fin 6) :
    (geometry M s t cStar).Ex P i = P.eval (xAt M s t cStar i) :=
  evalAt_eq_eval M hM _ P

private theorem eval_geometry_y (P : ℙ) (i : Fin 6) :
    (geometry M s t cStar).Ey P i = P.eval (yAt M s t cStar i) :=
  evalAt_eq_eval M hM _ P

theorem literal_reflected_clock (P : ℙ) :
    let g := geometry M s t cStar
    g.Ey ((1 - X) * P) = g.Ex X * g.Ey P := by
  dsimp only
  funext i
  change (geometry M s t cStar).Ey ((1 - X) * P) i =
    (geometry M s t cStar).Ex X i * (geometry M s t cStar).Ey P i
  simp only [eval_geometry_x M hM, eval_geometry_y M hM, eval_mul, eval_sub,
    eval_one, eval_X, xAt, Pi.sub_apply, Pi.one_apply]

theorem literal_quadrature_eight (h : ExactScalarSeed M s t cStar) :
    let g := geometry M s t cStar
    HasQuadratureOrder 8 g.W (g.Ex X) := by
  let g := geometry M s t cStar
  change HasQuadratureOrder 8 g.W (g.Ex X)
  intro k hk
  let y := yAt M s t cStar
  let x := xAt M s t cStar
  have hX : g.Ex X = x := evalSites_X M hM _
  have hmono : PolyBound 7 ((X : ℙ) ^ k) := by
    apply natDegree_le_iff_coeff_eq_zero.mp
    rw [natDegree_X_pow]
    omega
  have he := (literal_rule_exact7 M hM s t cStar h ((X ^ k).comp reflect)
    (comp_reflect_degree 7 _ hmono)).trans (mean_reflect M hM (X ^ k))
  have eq : (g.W ⬝ᵥ (g.Ex X) ^ k) = ((k + 1 : ℕ) : ℝ)⁻¹ := by
    rw [hX, ← mean_pow M hM]
    calc
      g.W ⬝ᵥ x ^ k = weightedEval (scalarWeights M y) y ((X ^ k).comp reflect) := by
        simp only [dotProduct, Pi.pow_apply, weightedEval_apply, eval_comp, Polynomial.eval_pow,
          eval_X, eval_reflect] <;> rfl
      _ = mean M (X ^ k) := he
  change ((k + 1 : ℕ) : ℝ) * (g.W ⬝ᵥ (g.Ex X) ^ k) = 1
  rw [eq, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))]

/-- Green cancellation is the rule applied to one polynomial derivative:
D[(I P)(I H ∘ reflect)], with both endpoint values zero. -/
theorem literal_green (h : ExactScalarSeed M s t cStar)
    (H P : ℙ) (n m : ℕ) (hH : PolyBound n H) (hP : PolyBound m P)
    (hBudget : n + m + 1 ≤ 7) :
    let g := geometry M s t cStar
    wDot g.W (g.Ex H) (g.Ey (g.I P)) = wDot g.W (g.Ex (g.I H)) (g.Ey P) := by
  let g := geometry M s t cStar
  let y := yAt M s t cStar
  let x := xAt M s t cStar
  let IH := coefficientPrimitive M H
  let IP := coefficientPrimitive M P
  let F := IP * IH.comp reflect
  have hIH := natDegree_le_iff_coeff_eq_zero.mpr
    (comp_reflect_degree (n + 1) IH (primitive_degree M hM n H hH))
  have hIP := natDegree_le_iff_coeff_eq_zero.mpr (primitive_degree M hM m P hP)
  have hF : F.natDegree ≤ (m + 1) + (n + 1) :=
    natDegree_mul_le.trans (Nat.add_le_add hIP hIH)
  have hDF : PolyBound 7 F.derivative := by
    apply natDegree_le_iff_coeff_eq_zero.mp
    exact (natDegree_derivative_le F).trans (by omega)
  have derF : F.derivative = P * IH.comp reflect - IP * H.comp reflect := by
    simp only [F, derivative_mul, derivative_comp, derivative_reflect, IH, IP,
      derivative_primitive M hM, neg_one_mul, mul_neg, sub_eq_add_neg]
  have end0 : F.eval 0 = 0 := by
    simp only [F, eval_mul, IP, primitive_eval_zero M hM, zero_mul]
  have end1 : F.eval 1 = 0 := by
    simp only [F, eval_mul, eval_comp, eval_reflect, sub_self, IH,
      primitive_eval_zero M hM, mul_zero]
  have meanZero : mean M F.derivative = 0 := by
    rw [mean_derivative M hM, end1, end0, sub_self]
  have pay := (literal_rule_exact7 M hM s t cStar h F.derivative hDF).trans meanZero
  have lhs (i : Fin 6) : g.Ex H i = H.eval (x i) := eval_geometry_x M hM s t cStar H i
  have rhs (i : Fin 6) : g.Ey P i = P.eval (y i) := eval_geometry_y M hM s t cStar P i
  have lih (i : Fin 6) : g.Ex (g.I H) i = IH.eval (x i) := eval_geometry_x M hM s t cStar IH i
  have lip (i : Fin 6) : g.Ey (g.I P) i = IP.eval (y i) := eval_geometry_y M hM s t cStar IP i
  have hx (i : Fin 6) : 1 - y i = x i := rfl
  have zeroDiff :
      wDot g.W (g.Ex (g.I H)) (g.Ey P) - wDot g.W (g.Ex H) (g.Ey (g.I P)) = 0 := by
    calc
      _ = weightedEval g.W y F.derivative := by
        simp only [wDot, weightedEval_apply, derF, eval_sub, eval_mul, eval_comp,
          eval_reflect, hx, lhs, rhs, lih, lip, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = 0 := pay
  exact (sub_eq_zero.mp zeroDiff).symm

end Green

/-- Exact scalar leaves supplied here to the pending literal Fin11
producer. Weight nonvanishing and the calibration cell are separate
leaves, neither assumed in this scalar proof. -/
structure QuadratureGreen (g : Geometry ℝ) : Prop where
  quadrature : HasQuadratureOrder 8 g.W (g.Ex X)
  clock : ∀ P : ℙ, g.Ey ((1 - X) * P) = (g.Ex X) * g.Ey P
  primitiveBound : ∀ (n : ℕ) (P : ℙ), PolyBound n P → PolyBound (n + 1) (g.I P)
  clockBound : ∀ (n : ℕ) (P : ℙ), PolyBound n P → PolyBound (n + 1) ((1 - X) * P)
  green : ∀ (H P : ℙ) (n m : ℕ), PolyBound n H → PolyBound m P → n + m + 1 ≤ 7 →
    wDot g.W (g.Ex H) (g.Ey (g.I P)) = wDot g.W (g.Ex (g.I H)) (g.Ey P)

/-- The actual six-site scalar constructor: only the standard basis
and literal exact algebraic seed, no supplied moments or weight rank. -/
theorem quadrature_green_of_exact_seed (M : MonomialBasis) (hM : standardPowers M)
    (s t cStar : ℝ) (seed : ExactScalarSeed M s t cStar) :
    QuadratureGreen (geometry M s t cStar) where
  quadrature := literal_quadrature_eight M hM s t cStar seed
  clock := literal_reflected_clock M hM s t cStar
  primitiveBound := primitive_degree M hM
  clockBound := clock_degree
  green := literal_green M hM s t cStar seed

end RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarQuadrature
