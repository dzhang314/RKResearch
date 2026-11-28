module

public import RKCert.ReviewedNative.DIRK12MidpointRealPhysicalWeights
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Exact conversion of polynomial quadrature on reflected coordinates
to the ordinary scalar moment premise of the reviewed flag theorem. -/
namespace RKResearch.Certified.DIRK12MidpointRealInterval

open Polynomial RKResearch Graded
open scoped Polynomial Matrix

section Field

variable {K : Type*} [Field K] [CharZero K]

theorem integral_monomial (n : Nat) (a : K) :
    integral (monomial n a) = a*((1/((n+1:Nat):ℚ):ℚ):K) := by
  rw [← C_mul_X_pow_eq_monomial,← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,integral_pow]

theorem integral_derivative (p : K[X]) :
    integral (Polynomial.derivative p)=p.eval 1-p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add,map_add,hp,hq,eval_add,eval_add]
    ring
  | monomial n a =>
    cases n with
    | zero => simp
    | succ n =>
      rw [derivative_monomial_succ,integral_monomial,eval_monomial,eval_monomial,
        one_pow,zero_pow (by omega),mul_one,mul_zero,sub_zero,
        Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
      have g : ((n+1:Nat):K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp [g]
      simp only [Nat.cast_add,Nat.cast_one]

theorem integral_reflected_power (j : Nat) :
    ((j+1:Nat):K)*integral ((1-X:K[X])^j)=1 := by
  have e := integral_derivative ((1-X:K[X])^(j+1))
  have d : Polynomial.derivative ((1-X:K[X])^(j+1)) =
      (-((j+1:Nat):K)) • ((1-X:K[X])^j) := by
    rw [derivative_pow_succ,map_sub,derivative_one,derivative_X,zero_sub,
      Polynomial.smul_eq_C_mul,map_neg]
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  rw [d,map_smul,smul_eq_mul] at e
  simp only [eval_pow,eval_sub,eval_one,eval_X,sub_self,sub_zero,one_pow] at e
  rw [zero_pow (by omega : j+1 ≠ 0),zero_sub] at e
  linear_combination -e

theorem ordinary_scalar_of_reflected {ι : Type*} [Fintype ι]
    (A : Matrix ι ι K) (b : ι → K)
    (paid : ∀ p : K[X], p.natDegree<12 → DIRK12MidpointStar.quadr A b p=integral p)
    (j : Nat) (hj : j < 12) :
    ((j+1:Nat):K)*row b ((nodes A)^j)=1 := by
  have deg : (1-X : K[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hpow : ((1-X : K[X])^j).natDegree < 12 := by
    rw [natDegree_pow]
    exact (Nat.mul_le_mul_left j deg).trans_lt (by simpa using hj)
  have h := paid ((1-X)^j) hpow
  rw [DIRK12MidpointStar.quadr_apply] at h
  simp only [eval_pow,eval_sub,eval_one,eval_X,sub_sub_cancel] at h
  have ident : row b ((nodes A)^j) = integral ((1-X)^j) := by
    rw [row_apply,dotProduct]
    simpa only [Pi.pow_apply] using h
  rw [ident]
  exact integral_reflected_power j

end Field

theorem ordinary_scalar_with_physical_weights {x f : ℝ}
    (hx : DirectedRatBox.Encloses xBox x) (hf : DirectedRatBox.Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0)
    (A : Matrix (Fin 15) (Fin 15) ℝ)
    (clocks : ∀ i, ¬ ghostRow i → 1-nodes A i=site x f (stageTag i)) :
    ∀ j < 12, ((j+1:Nat):ℝ)*row (physicalWeight x f) ((nodes A)^j)=1 :=
  ordinary_scalar_of_reflected A (physicalWeight x f)
    (scalar_and_star_with_physical_weights hx hf hx0 hf0 A clocks).1

end RKResearch.Certified.DIRK12MidpointRealInterval

#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.ordinary_scalar_of_reflected


#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.ordinary_scalar_with_physical_weights
