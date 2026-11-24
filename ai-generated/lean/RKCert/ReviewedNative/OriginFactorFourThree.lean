module

public import RKCert.ReviewedNative.NativeQuinticPorts
import Mathlib.Algebra.Polynomial.Div

@[expose] public section

/-! # The 4+3 primitive port on a polynomial vanishing at the origin -/

namespace RKCert.ReviewedNative.Quintic

open Polynomial RKResearch.Certified.Graded

noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- A polynomial of degree at most six that vanishes at zero is
excluded by the paid forward 4+3 windows at two distinct nonzero clocks.
The two raw multiplier caps are three and two, respectively. -/
theorem rooted_four_three (P : K[X]) (dp : P.natDegree≤6) (p0 : P.eval 0=0)
    {u v : K} (hu : u≠0) (hv : v≠0) (hvu : v≠u)
    (first : ∀ R : K[X], R.natDegree≤3 → (primitive (R*P)).eval u=0)
    (second : ∀ R : K[X], R.natDegree≤2 →
      (primitive ((R*(X-C u))*P)).eval v=0) : P=0 := by
  classical
  by_cases hp : P=0
  · exact hp
  have dvd : (X : K[X]) ∣ P := by rw [X_dvd_iff,coeff_zero_eq_eval_zero,p0]
  obtain ⟨J,factor⟩ := dvd
  have jn : J≠0 := fun h => hp (by rw [factor,h,mul_zero])
  have jd : J.natDegree≤5 := by
    rw [factor,natDegree_X_mul jn] at dp
    omega
  have j0 : J=0 := by
    refine quintic_four_three J jd hu hv hvu ?_ ?_
    · intro k
      have hk := k.isLt
      have d : ((X : K[X])^k.val).natDegree≤3 := by rw [natDegree_X_pow]; omega
      have m := first (X^k.val) d
      have eq : X^k.val*P = X^(k.val+1)*J := by
        rw [factor,pow_succ,mul_assoc]
      rwa [eq] at m
    · intro k
      have hk := k.isLt
      have d : ((X : K[X])^k.val).natDegree≤2 := by rw [natDegree_X_pow]; omega
      have m := second (X^k.val) d
      have eq : (X^k.val*(X-C u))*P = X^(k.val+1)*((X-C u)*J) := by
        rw [factor,pow_succ]
        ac_rfl
      rwa [eq] at m
  rw [factor,j0,mul_zero]

end
end RKCert.ReviewedNative.Quintic
