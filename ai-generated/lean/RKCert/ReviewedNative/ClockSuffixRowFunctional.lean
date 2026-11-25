module

public import RKCert.ReviewedNative.BushyMoments
public import RKCert.ReviewedNative.PositiveIntervalGrid19
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The actual weighted-column row functional

The polynomial test is derived from the reviewed bushy root cut and
ordinary bushy quadrature. No alternate order predicate or transposed
tableau order is used. -/

namespace RKResearch

open Polynomial
open RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open scoped BigOperators Matrix

noncomputable section

variable {ι K : Type*} [Fintype ι] [Field K]

namespace ClockLeakage

/-- The literal physical row sums of the tableau. -/
def clock (A : Matrix ι ι K) : ι → K :=
  A *ᵥ (1 : ι → K)

/-- Test a vector of physical input columns by the actual weighted
receiver rows. The test is linear in the vector, not in the tableau. -/
def rowFunctional (A : Matrix ι ι K) (b : ι → K) (F : K[X]) : (ι → K) →ₗ[K] K :=
  ∑ j, (b j * F.eval (clock A j)) • ((LinearMap.proj j).comp A.mulVecLin)

theorem rowFunctional_apply (A : Matrix ι ι K) (b : ι → K) (F : K[X]) (v : ι → K) :
    rowFunctional A b F v = ∑ j, b j * F.eval (clock A j) * (A *ᵥ v) j := by
  simp only [rowFunctional, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply]

private theorem agree_on_degree
    (L R : K[X] →ₗ[K] K) (P : K[X])
    (eq : ∀ n : ℕ, n ≤ P.natDegree → L (X ^ n) = R (X ^ n)) :
    L P = R P := by
  calc
    L P = ∑ n ∈ P.support, P.coeff n • L (X ^ n) := by
      conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
      simp only [← Polynomial.smul_eq_C_mul, map_sum, map_smul]
    _ = ∑ n ∈ P.support, P.coeff n • R (X ^ n) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [eq n (Polynomial.le_natDegree_of_mem_supp n hn)]
    _ = R P := by
      conv_rhs => rw [P.as_sum_support_C_mul_X_pow]
      simp only [← Polynomial.smul_eq_C_mul, map_sum, map_smul]

private def weightedEval (c w : ι → K) : K[X] →ₗ[K] K :=
  ∑ i, w i • Polynomial.leval (c i)

private theorem weightedEval_apply (c w : ι → K) (P : K[X]) :
    weightedEval c w P = ∑ i, w i * P.eval (c i) := by
  simp only [weightedEval, LinearMap.sum_apply, LinearMap.smul_apply,
    Polynomial.leval_apply, smul_eq_mul]

private theorem eval_pow_clock (c : ι → K) (n : ℕ) :
    (fun i => ((X : K[X]) ^ n).eval (c i)) = c ^ n := by
  funext i
  simp only [eval_pow, eval_X, Pi.pow_apply]

variable [CharZero K]

private def residualAt (A : Matrix ι ι K) (i : ι) : K[X] →ₗ[K] K :=
  (LinearMap.proj i).comp (A.mulVecLin.comp (LinearMap.pi fun j => Polynomial.leval (clock A j))) -
    (Polynomial.leval (clock A i)).comp formalPrimitiveLinear

private theorem residualAt_apply (A : Matrix ι ι K) (i : ι) (Q : K[X]) :
    residualAt A i Q = (A *ᵥ (fun j => Q.eval (clock A j))) i -
      (formalPrimitive Q).eval (clock A i) := rfl

private theorem primitive_pow_eval (n : ℕ) (x : K) :
    (formalPrimitive ((X : K[X]) ^ n)).eval x = x ^ (n + 1) / ((n + 1 : ℕ) : K) := by
  simp only [formalPrimitive, support_X_pow, Finset.sum_singleton, coeff_X_pow_self,
    eval_monomial, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul] <;> ring

variable {A : Matrix ι ι K} {b : ι → K} {p : ℕ}

private theorem exact_polynomial_moment (ho : HasOrder p A b) (G : K[X])
    (paid : G.natDegree + 1 ≤ p) :
    (∑ i, b i * G.eval (clock A i)) = integral 0 1 G := by
  have h : weightedEval (clock A) b G = integral 0 1 G := by
    apply agree_on_degree
    intro n hn
    calc
      weightedEval (clock A) b (X ^ n) = stageMass b (A *ᵥ 1) n := by
        simp only [weightedEval_apply, stageMass, dotProduct, eval_pow, eval_X,
          Pi.pow_apply, clock]
      _ = 1 / ((n + 1 : ℕ) : K) := ho.bushy_moment_div n (by omega)
      _ = integral 0 1 (X ^ n) := by rw [integral_zero_left, primitive_pow_eval, one_pow]
  simpa only [weightedEval_apply] using h

private theorem monomial_residual_zero (ho : HasOrder p A b) (d k : ℕ)
    (paid : d + 1 + (k + 1) ≤ p) :
    (∑ i, b i * ((A *ᵥ ((clock A) ^ d)) i -
      clock A i ^ (d + 1) / ((d + 1 : ℕ) : K)) * clock A i ^ k) = 0 := by
  let D : K := ((d + 1 : ℕ) : K)
  have Dne : D ≠ 0 := (ho.natCast_isUnit (n := d+1) (by omega) (by omega)).ne_zero
  have raw :
      (∑ i, b i * (D * (A *ᵥ ((clock A) ^ d)) i - clock A i ^ (d + 1)) * clock A i ^ k) = 0 := by
    simpa only [stageMass, dotProduct, monomialStageDefect, Pi.pow_apply, clock, D] using
      (ho.monomialStageDefect_moment d k paid)
  have expand :
      D * (∑ i, b i * ((A *ᵥ ((clock A) ^ d)) i - clock A i ^ (d + 1) / D) *
          clock A i ^ k) =
        ∑ i, b i * (D * (A *ᵥ ((clock A) ^ d)) i - clock A i ^ (d + 1)) * clock A i ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have cancel : D * (clock A i ^ (d + 1) / D) = clock A i ^ (d + 1) :=
      (mul_comm _ _).trans (div_mul_cancel₀ _ Dne)
    calc
      _ = b i * (D * (A *ᵥ ((clock A) ^ d)) i - D * (clock A i ^ (d + 1) / D)) *
            clock A i ^ k := by ring
      _ = _ := by rw [cancel]
  exact (mul_eq_zero.mp (expand.trans raw)).resolve_left Dne

private theorem paid_left_test (ho : HasOrder p A b) (Q F : K[X])
    (paid : Q.natDegree + F.natDegree + 2 ≤ p) :
    rowFunctional A b F (fun i => Q.eval (clock A i)) =
      ∑ i, b i * F.eval (clock A i) * integral 0 (clock A i) Q := by
  let W : K[X] →ₗ[K] K := ∑ i, (b i * F.eval (clock A i)) • residualAt A i
  have W_apply (G : K[X]) :
      W G = ∑ i, (b i * F.eval (clock A i)) * residualAt A i G := by
    simp only [W, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hz : W Q = 0 := by
    change W Q = (0 : K[X] →ₗ[K] K) Q
    apply agree_on_degree
    intro d hd
    let L := weightedEval (clock A) (fun i => b i * residualAt A i (X ^ d))
    have hL : L F = 0 := by
      change L F = (0 : K[X] →ₗ[K] K) F
      apply agree_on_degree
      intro k hk
      change weightedEval (clock A) (fun i => b i * residualAt A i (X ^ d)) (X ^ k) = 0
      rw [weightedEval_apply]
      simp only [residualAt_apply]
      rw [eval_pow_clock (clock A) d]
      simp only [eval_pow, eval_X, primitive_pow_eval]
      exact monomial_residual_zero ho d k (by omega)
    have reorder : W (X ^ d) = L F := by
      rw [W_apply]
      change _ = weightedEval (clock A) (fun i => b i * residualAt A i (X ^ d)) F
      rw [weightedEval_apply]
      apply Finset.sum_congr rfl
      intro i _
      ring
    change W (X ^ d) = 0
    exact reorder.trans hL
  have sum_zero : (∑ i, b i * F.eval (clock A i) *
      ((A *ᵥ (fun j => Q.eval (clock A j))) i - (formalPrimitive Q).eval (clock A i))) = 0 := by
    simpa only [W_apply, residualAt_apply] using hz
  simp only [mul_sub, Finset.sum_sub_distrib] at sum_zero
  simpa only [rowFunctional_apply, integral_zero_left] using sub_eq_zero.mp sum_zero

private theorem primitive_product (F Q : K[X]) :
    formalPrimitive (F * formalPrimitive Q + Q * formalPrimitive F) =
      formalPrimitive F * formalPrimitive Q := by
  apply eq_of_derivative_and_eval_zero
  · simp only [derivative_formalPrimitive, derivative_mul]
    ring
  · simp only [formalPrimitive_eval_zero, eval_mul, zero_mul]

private theorem primitive_swap (F Q : K[X]) :
    integral 0 1 (F * formalPrimitive Q) =
      integral 0 1 (Q * (C ((formalPrimitive F).eval 1) - formalPrimitive F)) := by
  have add : integral 0 1 (F * formalPrimitive Q) + integral 0 1 (Q * formalPrimitive F) =
      (formalPrimitive F).eval 1 * (formalPrimitive Q).eval 1 := by
    rw [← map_add, integral_zero_left, primitive_product, eval_mul]
  have right : integral 0 1 (Q * (C ((formalPrimitive F).eval 1) - formalPrimitive F)) =
      (formalPrimitive F).eval 1 * (formalPrimitive Q).eval 1 -
        integral 0 1 (Q * formalPrimitive F) := by
    rw [mul_sub, map_sub, mul_comm Q (C ((formalPrimitive F).eval 1)),
      ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul, integral_zero_left 1 Q]
  calc
    _ = (integral 0 1 (F * formalPrimitive Q) + integral 0 1 (Q * formalPrimitive F)) -
          integral 0 1 (Q * formalPrimitive F) := by ring
    _ = _ := by rw [add, ← right]

/-- One paid polynomial test of the literal weighted-column functional.
No family of proposed clock supports occurs in the statement. -/
theorem paid_rowFunctional_test (ho : HasOrder p A b) (Q F : K[X])
    (paid : Q.natDegree + F.natDegree + 2 ≤ p) :
    rowFunctional A b F (fun i => Q.eval (clock A i)) =
      ∑ i, b i * (Q.eval (clock A i) * integral (clock A i) 1 F) := by
  let U := F * formalPrimitive Q
  let V := Q * (C ((formalPrimitive F).eval 1) - formalPrimitive F)
  have uCost : U.natDegree + 1 ≤ p := by
    have d : U.natDegree ≤ F.natDegree + (formalPrimitive Q).natDegree := natDegree_mul_le
    have dQ := natDegree_formalPrimitive_le Q
    omega
  have vCost : V.natDegree + 1 ≤ p := by
    have inner : (C ((formalPrimitive F).eval 1) - formalPrimitive F).natDegree ≤
        F.natDegree + 1 := by
      exact (natDegree_sub_le _ _).trans (by
        rw [natDegree_C]
        exact max_le (Nat.zero_le _) (natDegree_formalPrimitive_le F))
    have d : V.natDegree ≤ Q.natDegree +
        (C ((formalPrimitive F).eval 1) - formalPrimitive F).natDegree := natDegree_mul_le
    omega
  calc
    _ = ∑ i, b i * F.eval (clock A i) * integral 0 (clock A i) Q :=
      paid_left_test ho Q F paid
    _ = ∑ i, b i * U.eval (clock A i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [U, eval_mul, integral_zero_left]
      ring
    _ = integral 0 1 U := exact_polynomial_moment ho U uCost
    _ = integral 0 1 V := primitive_swap F Q
    _ = ∑ i, b i * V.eval (clock A i) := (exact_polynomial_moment ho V vCost).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [V, eval_mul, eval_sub, eval_C, integral_apply]

end ClockLeakage
end
end RKResearch
