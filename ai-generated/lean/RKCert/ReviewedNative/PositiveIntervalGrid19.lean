module

public import RKCert.NodalPrimitive
public import RKCert.ReviewedNative.PositiveRationalRule19
public import Mathlib.Order.Interval.Set.Defs

import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Formal interval moments are finite exact positive sums

A tree-free consumer of the fixed positive unit rule. The antiderivative is
algebraic; in particular no Archimedean or real closed field is assumed.
-/
namespace RKCert.ReviewedNative.PositiveRule19

open Polynomial RKCert.Endpoint
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- Exact difference of normalized polynomial primitives at two endpoints. -/
def integral (l r : K) : K[X] →ₗ[K] K :=
  (Polynomial.leval r - Polynomial.leval l).comp formalPrimitiveLinear

@[simp] theorem integral_apply (l r : K) (P : K[X]) :
    integral l r P = (formalPrimitive P).eval r - (formalPrimitive P).eval l := rfl

@[simp] theorem integral_zero_left (r : K) (P : K[X]) :
    integral 0 r P = (formalPrimitive P).eval r := by
  rw [integral_apply, formalPrimitive_eval_zero, sub_zero]

/-- The same points and weights affinely rescaled. Positivity is only used
later, so all of the exact quadrature identities hold without an order. -/
def intervalPoint (l r : K) (i : Fin 19) := l + (r-l)*point K i

def intervalWeight (l r : K) (i : Fin 19) := (r-l)*weight K i


private theorem fp_C_mul (a : K) (P : K[X]) :
    formalPrimitive (C a*P) = C a*formalPrimitive P := by
  apply eq_of_derivative_and_eval_zero
  · simp [derivative_mul]
  · simp

/-- An oriented affine substitution for formal polynomial primitives. -/
theorem integral_affine (l r : K) (P : K[X]) :
    integral l r P = (r-l)*integral 0 1 (P.comp (C (r-l)*X+C l)) := by
  let L : K[X] := C (r-l)*X+C l
  let B := (formalPrimitive P).comp L - C ((formalPrimitive P).eval l)
  have l0 : L.eval 0 = l := by simp [L]
  have l1 : L.eval 1 = r := by simp [L]
  have ld : L.derivative = C (r-l) := by simp [L]
  have e : B = formalPrimitive (C (r-l)*(P.comp L)) := by
    apply eq_of_derivative_and_eval_zero
    · rw [derivative_formalPrimitive]
      simp only [B,map_sub,derivative_comp,derivative_formalPrimitive,derivative_C,sub_zero,
        ld]
    · simp [B, eval_comp, l0]
  have h := congrArg (Polynomial.eval (1 : K)) e
  change ((formalPrimitive P).comp L-C ((formalPrimitive P).eval l)).eval 1 =
    (formalPrimitive (C (r-l)*(P.comp L))).eval 1 at h
  simp only [eval_sub,eval_comp,l1,eval_C,fp_C_mul,eval_mul] at h
  change (formalPrimitive P).eval r-(formalPrimitive P).eval l =
    (r-l)*integral 0 1 (P.comp L)
  rw [integral_zero_left]
  exact h

/-- Reflection has the precise reversed endpoint, not an unsigned interval
or a substitution of a different primitive normalization. -/
theorem integral_reflect (P : K[X]) (x : K) :
    integral 0 (1-x) (P.comp (1-X)) = integral x 1 P := by
  let L : K[X] := 1-X
  let B := C ((formalPrimitive P).eval 1) - (formalPrimitive P).comp L
  have ld : L.derivative = -1 := by simp [L]
  have e : formalPrimitive (P.comp L) = B := by
    apply eq_of_derivative_and_eval_zero
    · rw [derivative_formalPrimitive]
      simp only [B,map_sub,derivative_comp,derivative_formalPrimitive,derivative_C,zero_sub,
        ld,neg_one_mul,neg_neg]
    · simp [B,L,eval_comp]
  rw [integral_zero_left,integral_apply]
  change (formalPrimitive (P.comp L)).eval (1-x) = _
  rw [e]
  simp [B,L,eval_comp]

private theorem at_one_monomial (j : ℕ) (a : K) :
    integral 0 1 (monomial j a) = a/((j+1:ℕ):K) := by
  by_cases h : a=0
  · simp [h, formalPrimitive]
  rw [integral_zero_left]
  simp [formalPrimitive, support_monomial j h]

/-- Unit exactness on the entire polynomial space through degree nineteen. -/
theorem unit_exact (P : K[X]) (hp : P.natDegree≤19) :
    integral 0 1 P = ∑ i : Fin 19, weight K i*P.eval (point K i) := by
  let L : K[X] →ₗ[K] K := ∑ i : Fin 19, weight K i • Polynomial.leval (point K i)
  have app (S : K[X]) : L S = ∑ i : Fin 19, weight K i*S.eval (point K i) := by
    simp [L, LinearMap.sum_apply, smul_eq_mul]
  rw [←app P]
  rw [P.as_sum_range' 20 (Nat.lt_succ_of_le hp), map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [app,at_one_monomial]
  simp only [eval_monomial]
  have m := exact_monomial K ⟨j, Finset.mem_range.mp hj⟩
  change (∑ i : Fin 19, weight K i*point K i^j) = 1/((j+1:ℕ):K) at m
  simp_rw [show ∀ i : Fin 19, weight K i*(P.coeff j*point K i^j) =
      P.coeff j*(weight K i*point K i^j) from fun i => by ac_rfl]
  rw [←Finset.mul_sum,m, mul_one_div]

/-- Algebraic quadrature, without any restriction on the relative endpoints. -/
theorem interval_exact (l r : K) (P : K[X]) (hp : P.natDegree≤19) :
    integral l r P = ∑ i : Fin 19, intervalWeight l r i*P.eval (intervalPoint l r i) := by
  let L : K[X] := C (r-l)*X+C l
  have dL : L.natDegree≤1 := by
    dsimp only [L]
    apply natDegree_add_le_of_degree_le
    · simpa using (natDegree_mul_le (p:=C (r-l)) (q:=X))
    · simp
  have dp : (P.comp L).natDegree≤19 := by
    exact natDegree_comp_le.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul hp dL)
  rw [integral_affine l r P]
  change (r-l)*integral 0 1 (P.comp L) = _
  rw [unit_exact _ dp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [intervalWeight, intervalPoint, L, eval_comp, add_comm l, mul_assoc]

end

section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {l r : K}

theorem intervalPoint_mem (lr : l<r) (i : Fin 19) :
    intervalPoint l r i ∈ Set.Ioo l r := by
  have h := sub_pos.mpr lr
  have p := mul_pos h (point_pos K i)
  have q := mul_lt_mul_of_pos_left (point_lt_one K i) h
  change l < l+(r-l)*point K i ∧ l+(r-l)*point K i < r
  constructor
  · exact lt_add_of_pos_right _ p
  · linarith only [q]

theorem intervalPoint_strictMono (lr : l<r) : StrictMono (intervalPoint l r) := by
  intro i j ij
  change l+(r-l)*point K i < l+(r-l)*point K j
  have e := mul_lt_mul_of_pos_left (point_strictMono K ij) (sub_pos.mpr lr)
  linarith only [e]

theorem intervalWeight_pos (lr : l<r) (i : Fin 19) : 0 < intervalWeight l r i :=
  mul_pos (sub_pos.mpr lr) (weight_pos K i)

end Ordered
end RKCert.ReviewedNative.PositiveRule19
