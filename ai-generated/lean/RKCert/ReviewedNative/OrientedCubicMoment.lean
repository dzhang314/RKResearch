module

public import RKCert.NodalPrimitive
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Positive oriented moment for a nonzero cubic

This is an exact triangular sum of squares for four coefficients,
not numerical integration or a determinant certificate. The rescaling
uses an even power of the endpoint, so negative clocks also work. -/
namespace RKCert.Endpoint
open Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem primitiveLinear_monomial (n : ℕ) (a : K) :
    formalPrimitiveLinear (monomial n a) = monomial (n+1) (a/((n+1:ℕ):K)) := by
  by_cases ha : a=0
  · simp [ha]
  · change formalPrimitive (monomial n a) = _
    simp [formalPrimitive,support_monomial n ha]

private theorem cubic_gram_identity (a : Fin 4 → K) :
    (∑ i : Fin 4, ∑ j : Fin 4, a i*a j/((i.val+j.val+2:ℕ):K)) =
    (a 0 + (2/3:K)*a 1 + (1/2:K)*a 2 + (2/5:K)*a 3)^2/2 +
    (a 1 + (6/5:K)*a 2 + (6/5:K)*a 3)^2/36 +
    (a 2 + (12/7:K)*a 3)^2/600 +
    (a 3)^2/9800 := by
  simp only [Fin.sum_univ_four]
  norm_num [Fin.val_zero,Fin.val_one]
  ring

private theorem cubic_gram_pos (a : Fin 4 → K) (ha : a≠0) :
    0 < ∑ i : Fin 4, ∑ j : Fin 4, a i*a j/((i.val+j.val+2:ℕ):K) := by
  let f0 := a 0 + (2/3:K)*a 1 + (1/2:K)*a 2 + (2/5:K)*a 3
  let f1 := a 1 + (6/5:K)*a 2 + (6/5:K)*a 3
  let f2 := a 2 + (12/7:K)*a 3
  let f3 := a 3
  rw [cubic_gram_identity]
  change 0 < f0^2/2 + f1^2/36 + f2^2/600 + f3^2/9800
  have n0 : 0 ≤ f0^2/2 := div_nonneg (sq_nonneg _) (by norm_num)
  have n1 : 0 ≤ f1^2/36 := div_nonneg (sq_nonneg _) (by norm_num)
  have n2 : 0 ≤ f2^2/600 := div_nonneg (sq_nonneg _) (by norm_num)
  have n3 : 0 ≤ f3^2/9800 := div_nonneg (sq_nonneg _) (by norm_num)
  by_contra! no
  have z3 : f3=0 := by
    by_contra nz
    have pos : 0 < f3^2/9800 := div_pos (sq_pos_of_ne_zero nz) (by norm_num)
    linarith
  have z2 : f2=0 := by
    by_contra nz
    have pos : 0 < f2^2/600 := div_pos (sq_pos_of_ne_zero nz) (by norm_num)
    linarith
  have z1 : f1=0 := by
    by_contra nz
    have pos : 0 < f1^2/36 := div_pos (sq_pos_of_ne_zero nz) (by norm_num)
    linarith
  have z0 : f0=0 := by
    by_contra nz
    have pos : 0 < f0^2/2 := div_pos (sq_pos_of_ne_zero nz) (by norm_num)
    linarith
  have a3 : a 3=0 := z3
  have a2 : a 2=0 := by simpa only [f2,a3,mul_zero,add_zero] using z2
  have a1 : a 1=0 := by simpa only [f1,a3,a2,mul_zero,add_zero] using z1
  have a0 : a 0=0 := by simpa only [f0,a3,a2,a1,mul_zero,add_zero] using z0
  exact ha (funext (fun i => by fin_cases i <;> assumption))

private theorem cubic_moment_expanded [DecidableEq K] (a : Fin 4 → K) (x : K) :
    (formalPrimitive (X*(ofFn 4 a)^2)).eval x =
      x^2*(∑ i : Fin 4, ∑ j : Fin 4,
        (a i*x^i.val)*(a j*x^j.val)/((i.val+j.val+2:ℕ):K)) := by
  have h : X*(ofFn 4 a)^2 =
      ∑ i : Fin 4, ∑ j : Fin 4, monomial (i.val+j.val+1) (a i*a j) := by
    rw [pow_two,ofFn_eq_sum_monomial,Finset.sum_mul,Finset.mul_sum]
    simp_rw [Finset.mul_sum,monomial_mul_monomial]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [←pow_one X,X_pow_mul_monomial]
  change (formalPrimitiveLinear (X*(ofFn 4 a)^2)).eval x = _
  rw [h,map_sum,eval_finsetSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum,eval_finsetSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [primitiveLinear_monomial,eval_monomial]
  change a i*a j/((i.val+j.val+2:ℕ):K)*x^(i.val+j.val+2)=_
  rw [pow_add,pow_add]
  ring

theorem primitive_x_cubic_square_pos (P : K[X]) (deg : P.natDegree≤3) (pn : P≠0)
    {x : K} (xn : x≠0) : 0 < (formalPrimitive (X*P^2)).eval x := by
  classical
  let a : Fin 4 → K := fun i => P.coeff i.val
  have repr : ofFn 4 a=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  let v : Fin 4 → K := fun i => a i*x^i.val
  have vn : v≠0 := by
    intro z
    have az : a=0 := by
      ext i
      exact (mul_eq_zero.mp (congrFun z i)).resolve_right (pow_ne_zero _ xn)
    exact pn (repr ▸ (by rw [az,map_zero]))
  rw [←repr,cubic_moment_expanded]
  exact mul_pos (sq_pos_of_ne_zero xn) (cubic_gram_pos v vn)

end RKCert.Endpoint
