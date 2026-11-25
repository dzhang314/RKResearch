module

public import RKCert.ReviewedNative.GradedPrimitives
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.Polynomial.ScaleRoots

import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Integral reciprocal coordinates for the native first primitive

A monic scaled reciprocal has roots a/r and coefficients
p[d-i]*a^(d-i)/p[0]. The cleared first-primitive equation is a sum
in the coefficient ring, so it can be reduced in a residue field.
There is no fixed orthogonal polynomial or norm in this module.
-/
namespace RKResearch.Certified.Graded.NativeReciprocal

open Polynomial
open scoped BigOperators

noncomputable section

variable {E : Type*} [Field E]

def scaledReciprocal (P : E[X]) (a : E) : E[X] :=
  C (P.coeff 0)⁻¹ * P.reverse.scaleRoots a

theorem scaledReciprocal_degree {P : E[X]} (p0 : P.coeff 0≠0) (a : E) :
    (scaledReciprocal P a).natDegree=P.natDegree := by
  rw [scaledReciprocal,natDegree_C_mul (inv_ne_zero p0),natDegree_scaleRoots,
    reverse_natDegree,natTrailingDegree_eq_zero.mpr (Or.inr p0),Nat.sub_zero]

theorem scaledReciprocal_monic {P : E[X]} (p0 : P.coeff 0≠0) (a : E) :
    (scaledReciprocal P a).Monic := by
  change (scaledReciprocal P a).leadingCoeff=1
  rw [scaledReciprocal,leadingCoeff_mul,leadingCoeff_C,leadingCoeff_scaleRoots,
    reverse_leadingCoeff,trailingCoeff_eq_coeff_zero p0,inv_mul_cancel₀ p0]

theorem scaledReciprocal_coeff {P : E[X]} (p0 : P.coeff 0≠0) (a : E)
    {j : ℕ} (pay : j≤P.natDegree) :
    (scaledReciprocal P a).coeff j =
      (P.coeff 0)⁻¹*(P.coeff (P.natDegree-j)*a^(P.natDegree-j)) := by
  rw [scaledReciprocal,coeff_C_mul,coeff_scaleRoots,coeff_reverse,revAt_le pay,
    reverse_natDegree,natTrailingDegree_eq_zero.mpr (Or.inr p0),Nat.sub_zero]

theorem scaledReciprocal_mul (P Q : E[X]) (a : E) :
    scaledReciprocal (P*Q) a=scaledReciprocal P a*scaledReciprocal Q a := by
  have coeff0 : (P*Q).coeff 0=P.coeff 0*Q.coeff 0 := by
    simp only [coeff_zero_eq_eval_zero,eval_mul]
  simp only [scaledReciprocal,coeff0,reverse_mul_of_domain,
    mul_scaleRoots_of_noZeroDivisors,mul_inv_rev,C_mul]
  ring

theorem scaledReciprocal_isRoot_iff {P : E[X]} (p0 : P.coeff 0≠0)
    {a t : E} (a0 : a≠0) (t0 : t≠0) :
    (scaledReciprocal P a).IsRoot t ↔ P.IsRoot (a/t) := by
  let y := a/t
  letI : Invertible y := invertibleOfNonzero (div_ne_zero a0 t0)
  have yInv : ⅟y=t/a := by
    rw [invOf_eq_inv]
    dsimp only [y]
    rw [inv_div]
  have h := eval₂_reverse_eq_zero_iff (RingHom.id E) y P
  rw [yInv,eval₂_id,eval₂_id] at h
  have sc := scaleRoots_eval_mul P.reverse (t/a) a
  rw [show a*(t/a)=t from by rw [mul_comm,div_mul_cancel₀ _ a0]] at sc
  change (scaledReciprocal P a).eval t=0 ↔ P.eval y=0
  rw [scaledReciprocal,eval_mul,eval_C,sc,mul_eq_zero,
    or_iff_right (inv_ne_zero p0),mul_eq_zero,or_iff_right (pow_ne_zero _ a0)]
  exact h

/-- Integers 420/(k+2), for the original degree at most five. -/
def clearedFactors : Fin 6 → ℤ := ![210,140,105,84,70,60]

/-- Multiplication by 420 clears all primitive denominators. Reading
the reciprocal coefficient in index 5-k costs no factor of t⁻¹ here. -/
def clearedFirst {B : Type*} [CommRing B] (R : B[X]) (t : B) : B :=
  ∑ k : Fin 6, (clearedFactors k : B)*R.coeff (5-k.val)*t^(5-k.val)

theorem map_clearedFirst {B D : Type*} [CommRing B] [CommRing D]
    (f : B →+* D) (R : B[X]) (t : B) :
    f (clearedFirst R t)=clearedFirst (R.map f) (f t) := by
  simp only [clearedFirst,map_sum,map_mul,map_pow,map_intCast,coeff_map]

theorem clearedFirst_X_five {B : Type*} [CommRing B] (t : B) :
    clearedFirst ((X:B[X])^5) t=210*t^5 := by
  unfold clearedFirst
  rw [Finset.sum_eq_single (0:Fin 6)]
  · simp [clearedFactors,coeff_X_pow]
  · intro i _ ni
    have i0 : i.val≠0 := fun h => ni (Fin.ext h)
    have n : 5-i.val≠5 := by have hi := i.isLt; omega
    simp [coeff_X_pow,n]
  · simp

private theorem first_eval_five {P : E[X]} (degree : P.natDegree≤5) (u : E) :
    (primitive (X*P)).eval u =
      ∑ i : Fin 6, P.coeff i.val/((i.val+2:ℕ):E)*u^(i.val+2) := by
  classical
  have lt : P.natDegree < 6 := Nat.lt_succ_of_le degree
  let c := toFn 6 P
  have rep : ofFn 6 c=P := ofFn_comp_toFn_eq_id_of_natDegree_lt lt
  conv_lhs => rw [←rep,ofFn_eq_sum_monomial,Finset.mul_sum,map_sum,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  change (primitive (X*monomial i.val (P.coeff i.val))).eval u=_
  simp only [X_mul_monomial,primitive_monomial,eval_monomial,Nat.add_assoc,Nat.reduceAdd]

/-- This consumes the literal zero from the native primitive, with scale
a=9 and degree five. Only six elementary denominator identities enter. -/
theorem clearedFirst_of_primitive_zero [CharZero E]
    {P : E[X]} (degree : P.natDegree=5) (p0 : P.coeff 0≠0)
    {t : E} (t0 : t≠0) (zero : (primitive (X*P)).eval (9/t)=0) :
    clearedFirst (scaledReciprocal P 9) t=0 := by
  let m : E := 420*(P.coeff 0)⁻¹*t^7/81
  have id : clearedFirst (scaledReciprocal P 9) t =
      m*(primitive (X*P)).eval (9/t) := by
    rw [first_eval_five degree.le,clearedFirst,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have paid : 5-i.val≤P.natDegree := by rw [degree]; omega
    have term : P.natDegree-(5-i.val)=i.val := by
      rw [degree]
      have hi := i.isLt
      omega
    rw [scaledReciprocal_coeff p0 9 paid,term]
    fin_cases i <;> norm_num [m,clearedFactors] <;> field_simp [t0,p0] <;> ring
  rw [id,zero,mul_zero]

end
end RKResearch.Certified.Graded.NativeReciprocal
