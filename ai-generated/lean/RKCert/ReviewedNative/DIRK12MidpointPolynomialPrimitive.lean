module

public import RKCert.ReviewedNative.DIRK12MidpointNormalizedScalar
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! A polynomial primitive measured from a reflected clock to 1.
Its exact tests are paid by polynomial integration by parts. -/
namespace RKResearch.Certified.DIRK12MidpointProbes

open Polynomial DIRK12MidpointRealInterval
open scoped Polynomial BigOperators

variable {K : Type*} [Field K] [CharZero K]

noncomputable def anti : K[X] →ₗ[K] K[X] :=
  Polynomial.lsum fun k => LinearMap.id.smulRight
    ((((1/((k+1:Nat):ℚ):ℚ):K)) • (X:K[X])^(k+1))

theorem anti_monomial (n : Nat) (a : K) :
    anti (monomial n a)=monomial (n+1) (a/((n+1:Nat):K)) := by
  rw [anti,Polynomial.lsum_apply,Polynomial.sum_monomial_index]
  · simp only [LinearMap.smulRight_apply,LinearMap.id_coe,id_eq,smul_smul]
    rw [X_pow_eq_monomial,Polynomial.smul_monomial]
    push_cast
    simp [smul_eq_mul,div_eq_mul_inv]
  · simp [LinearMap.smulRight_apply]

theorem derivative_anti (p : K[X]) : Polynomial.derivative (anti p)=p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add,map_add,hp,hq]
  | monomial n a =>
    have nz : ((n+1:Nat):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
    have e : (n:K)+1=((n+1:Nat):K) := by push_cast; rfl
    rw [anti_monomial,derivative_monomial_succ,e,div_mul_cancel₀ _ nz]

theorem anti_one (p : K[X]) : (anti p).eval 1=integral p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add,map_add,eval_add,hp,hq]
  | monomial n a =>
    rw [anti_monomial,eval_monomial,one_pow,mul_one,integral_monomial]
    push_cast
    ring

omit [CharZero K] in
theorem anti_degree (p : K[X]) : (anti p).natDegree≤p.natDegree+1 := by
  rw [anti,Polynomial.lsum_apply,Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  simp only [LinearMap.smulRight_apply,LinearMap.id_coe,id_eq,smul_smul]
  have e : i≤p.natDegree := Polynomial.le_natDegree_of_ne_zero (mem_support_iff.mp hi)
  rw [Polynomial.smul_eq_C_mul]
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

noncomputable def fromOne (p : K[X]) : K[X] := C (integral p)-anti p

theorem fromOne_eval (p : K[X]) : (fromOne p).eval 1=0 := by
  simp [fromOne,anti_one]

theorem fromOne_derivative (p : K[X]) : Polynomial.derivative (fromOne p)=-p := by
  simp [fromOne,derivative_anti]

omit [CharZero K] in
theorem fromOne_degree (p : K[X]) : (fromOne p).natDegree≤p.natDegree+1 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  rw [Polynomial.natDegree_C]
  exact max_le (by omega) (anti_degree p)

theorem fromOne_paid (p : K[X]) (k : Nat) :
    integral ((X:K[X])^k*fromOne p)=integral ((X:K[X])^(k+1)*p)/((k+1:Nat):K) := by
  have h := integral_derivative ((X:K[X])^(k+1)*fromOne p)
  have e :
      Polynomial.derivative ((X:K[X])^(k+1)*fromOne p) =
        ((k+1:Nat):K) • ((X:K[X])^k*fromOne p)-(X:K[X])^(k+1)*p := by
    rw [derivative_mul,derivative_pow_succ,derivative_X,fromOne_derivative,
      Polynomial.smul_eq_C_mul]
    simp only [mul_one,Nat.cast_add,Nat.cast_one]
    ring
  rw [e,map_sub,map_smul,smul_eq_mul] at h
  simp only [eval_mul,eval_pow,eval_X,one_pow,fromOne_eval,one_mul,
    zero_pow (by omega : k+1≠0),zero_mul,sub_zero] at h
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (by omega : k+1≠0))).2
  linear_combination h

end RKResearch.Certified.DIRK12MidpointProbes

#print axioms RKResearch.Certified.DIRK12MidpointProbes.fromOne_paid
#print axioms RKResearch.Certified.DIRK12MidpointProbes.fromOne_degree
