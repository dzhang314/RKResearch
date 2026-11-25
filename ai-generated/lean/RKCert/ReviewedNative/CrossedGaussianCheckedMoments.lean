module

public import RKCert.ReviewedNative.CrossedGaussianRational
public import RKCert.ReviewedNative.PositiveIntervalGrid19
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Checked rational integration model for the signed localizer -/
namespace RKCert.ReviewedNative.CrossedGaussianCheckedMoments

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianLocalizer
open RKCert.ReviewedNative.CrossedGaussianMomentLift
open RKCert.ReviewedNative.CrossedGaussianRational
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def centerRef (K : Type*) [Field K] [CharZero K] : K[X] →ₗ[K] K :=
  ((3:K)/4) • (integral (-1) 1).comp (LinearMap.mulLeft K (1-(X:K[X])^2))

theorem centerRef_apply (P : K[X]) :
    centerRef K P = ((3:K)/4) * integral (-1) 1 ((1-X^2)*P) := rfl

private theorem centered_positive_deg (P : K[X]) (d : P.natDegree ≤ 12) :
    ((1-X^2)*P).natDegree ≤ 19 := by
  have hw : (1-(X:K[X])^2).natDegree ≤ 2 := (natDegree_sub_le _ _).trans (by simp)
  exact (natDegree_mul_le_of_le hw d).trans (by decide)

theorem centerRef_nonneg : ReferenceNonneg (centerRef K) := by
  intro P deg nn
  rw [centerRef_apply, interval_exact _ _ _ (centered_positive_deg P deg)]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  have lr : (-(1:K)) < 1 := by norm_num
  have hb := intervalPoint_mem lr i
  let y := intervalPoint (-(1:K)) 1 i
  have hy₀ : -1 < y := hb.1
  have hy₁ : y < 1 := hb.2
  have hW : 0 ≤ 1-y^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hy₁.le) (show 0 ≤ 1+y by linarith only [hy₀])
    nlinarith only [hh]
  simp only [eval_mul,eval_sub,eval_one,eval_pow,eval_X]
  exact mul_nonneg (intervalWeight_pos lr i).le (mul_nonneg hW (nn y))

private theorem primitive_X_pow (n : ℕ) :
    formalPrimitive ((X:K[X])^n) = monomial (n+1) (1/((n:K)+1)) := by
  rw [← monomial_one_right_eq_X_pow]
  simp [formalPrimitive,support_monomial n (one_ne_zero : (1:K) ≠ 0)]

private theorem centered_int_monomial (n : ℕ) :
    integral (-1) 1 ((X:K[X])^n) =
      (1/((n:K)+1)) * (1-(-1:K)^(n+1)) := by
  rw [integral_apply,primitive_X_pow]
  simp only [eval_monomial,one_pow,mul_one]
  ring

theorem centerRef_powers : ReferencePowers (centerRef K) := by
  intro n hn
  rw [centerRef_apply,
    show (1-(X:K[X])^2)*X^n = X^n-X^(n+2) by rw [pow_add]; ring,
    map_sub,centered_int_monomial,centered_int_monomial]
  interval_cases n <;> norm_num [refMoment]

def centerMap (K : Type*) [Field K] : K[X] := C (2:K)*X-1

private theorem centerMap_affine : (C ((1:K)-(-1))*X+C (-1) : K[X]) = centerMap K := by
  simp only [centerMap,map_neg,C_1]
  norm_num <;> ring

private theorem centerMap_reflect : (centerMap K).comp (1-X) = -centerMap K := by
  unfold centerMap
  rw [sub_comp, mul_comp, C_comp, X_comp, one_comp]
  norm_num [C_ofNat] <;> ring

private theorem centered_integral_neg_comp (P : K[X]) :
    integral (-(1:K)) 1 (P.comp (-X)) = integral (-1) 1 P := by
  have eq :
      (P.comp (-X)).comp (centerMap K) = (P.comp (centerMap K)).comp (1-X) := by
    rw [comp_assoc,neg_comp,X_comp,comp_assoc,centerMap_reflect]
  calc
    integral (-(1:K)) 1 (P.comp (-X)) =
        (1-(-1:K))*integral 0 1 ((P.comp (-X)).comp (centerMap K)) := by
      rw [integral_affine (-1) 1 (P.comp (-X)),centerMap_affine]
    _ = (1-(-1:K))*integral 0 1 (P.comp (centerMap K)) := by
      rw [eq]
      rw [show integral 0 1 ((P.comp (centerMap K)).comp (1-X)) =
          integral 0 1 (P.comp (centerMap K)) by
        simpa only [sub_zero] using integral_reflect (P.comp (centerMap K)) 0]
    _ = integral (-1) 1 P := by rw [integral_affine (-1) 1 P,centerMap_affine]

theorem centerRef_even (P : K[X]) :
    centerRef K (P.comp (-X)) = centerRef K P := by
  have eq : (1-X^2)*(P.comp (-X)) = ((1-X^2)*P).comp (-X) := by
    simp only [mul_comp,sub_comp,one_comp,pow_comp,X_comp]
    ring
  rw [centerRef_apply,centerRef_apply,eq,centered_integral_neg_comp]

theorem centerRef_pullback (P : K[X]) :
    centerRef K P = (6:K)*integral 0 1 (X*(1-X)*(P.comp (centerMap K))) := by
  have eq :
      ((1-X^2)*P).comp (centerMap K) =
        C (4:K)*(X*(1-X)*(P.comp (centerMap K))) := by
    simp only [mul_comp,sub_comp,one_comp,pow_comp,X_comp,centerMap,C_ofNat]
    ring
  rw [centerRef_apply,integral_affine (-1) 1 ((1-X^2)*P),centerMap_affine,eq,moment_C_mul]
  ring

end
end RKCert.ReviewedNative.CrossedGaussianCheckedMoments
