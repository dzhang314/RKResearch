module

public import RKCert.ReviewedNative.PositiveIntervalGrid19

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact exterior barycenter from the original inner primitive

This is a universal algebraic mean on the negative interval. The three
positive roots may be any ordered-field values and are not inserted in
a reference polynomial. No numerical classification of the profile
or sign of its RK quadrature weights is needed. -/
namespace RKCert.ReviewedNative.WeakFiveSoleInner

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open scoped Polynomial

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
set_option maxHeartbeats 1400000

def cubic (x₀ x₁ x₂ : K) : K[X] := (X-C x₀)*(X-C x₁)*(X-C x₂)

private theorem negate_interval (P : K[X]) (A : K) :
    integral (-A) 0 P = integral 0 A (P.comp (-X)) := by
  have f : formalPrimitive (P.comp (-X)) = -(formalPrimitive P).comp (-X) := by
    apply eq_of_derivative_and_eval_zero
    · simp only [derivative_formalPrimitive,map_neg,derivative_comp,derivative_X,
        neg_one_mul,neg_neg]
    · simp only [formalPrimitive_eval_zero,eval_neg,eval_comp,eval_X,neg_zero]
  rw [integral_apply,integral_zero_left,f,eval_neg,eval_comp,eval_neg,eval_X,
    formalPrimitive_eval_zero,zero_sub]

private theorem int_pow (A : K) (j : ℕ) :
    integral 0 A ((X:K[X])^j) = A^(j+1)/((j:K)+1) := by
  have fp : formalPrimitive ((X:K[X])^j) = monomial (j+1) (1/((j:K)+1)) := by
    rw [← monomial_one_right_eq_X_pow]
    simp [formalPrimitive,support_monomial j (one_ne_zero : (1:K)≠0)]
  rw [integral_zero_left,fp,eval_monomial]
  simp only [div_eq_mul_inv,one_mul]
  exact mul_comm _ _

private theorem int_C_pow (A c : K) (j : ℕ) :
    integral 0 A (C c*X^j) = c*(A^(j+1)/((j:K)+1)) := by
  rw [← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,int_pow]

private theorem int_bin (A E c : K) (j : ℕ) :
    integral 0 A ((X-C E)*(C c*X^j)) =
      (c*(A^(j+1)/((j:K)+1)))*(A*((j:K)+1)/((j:K)+2)-E) := by
  have p : (X-C E)*(C c*X^j) = C c*X^(j+1)-C (E*c)*X^j := by
    rw [pow_succ,map_mul]
    ring
  rw [p,map_sub,int_C_pow,int_C_pow,pow_succ A (j+1)]
  simp only [Nat.cast_add,Nat.cast_one]
  have hd₁ : (j:K)+1 ≠ 0 := (by positivity : 0 < (j:K)+1).ne'
  have hd₂ : (j:K)+1+1 ≠ 0 := (by positivity : 0 < (j:K)+1+1).ne'
  have hd₃ : (j:K)+2 ≠ 0 := (by positivity : 0 < (j:K)+2).ne'
  field_simp [hd₁,hd₂,hd₃] <;> ring

/-- The strict two-sided exterior scale costs exactly the **actual**
forward-inner equation. After negating the integration variable, the
five coefficient weights are positive, so the five exact monomial
means lie strictly between their extremal weighted average. -/
theorem exterior_mean_bounds {a e u x₀ x₁ x₂ : K}
    (a₀ : a < 0) (u₀ : 0 < u) (h₀ : 0 < x₀) (h₁ : 0 < x₁) (h₂ : 0 < x₂)
    (paid : integral 0 a (X*(X-C u)*((X-C e)*cubic x₀ x₁ x₂))=0) :
    (2:K)/3*(-a) < -e ∧ -e < (6:K)/7*(-a) := by
  let A := -a
  let E := -e
  let s := x₀+x₁+x₂
  let p := x₀*x₁+x₀*x₂+x₁*x₂
  let t := x₀*x₁*x₂
  let c₁ := u*t
  let c₂ := t+u*p
  let c₃ := p+u*s
  let c₄ := s+u
  have Ap : 0 < A := neg_pos.mpr a₀
  have sp : 0 < s := add_pos (add_pos h₀ h₁) h₂
  have pp : 0 < p := add_pos (add_pos (mul_pos h₀ h₁) (mul_pos h₀ h₂)) (mul_pos h₁ h₂)
  have tp : 0 < t := mul_pos (mul_pos h₀ h₁) h₂
  have p₁ : 0 < c₁ := mul_pos u₀ tp
  have p₂ : 0 < c₂ := add_pos tp (mul_pos u₀ pp)
  have p₃ : 0 < c₃ := add_pos pp (mul_pos u₀ sp)
  have p₄ : 0 < c₄ := add_pos sp u₀
  let F : K[X] := X*(X-C u)*((X-C e)*cubic x₀ x₁ x₂)
  let V : K[X] := C c₁*X^1+C c₂*X^2+C c₃*X^3+C c₄*X^4+C (1:K)*X^5
  have eq : F.comp (-X) = (X-C E)*V := by
    simp only [F,V,cubic,E,c₁,c₂,c₃,c₄,t,p,s,mul_comp,sub_comp,C_comp,X_comp,
      map_neg,map_mul,map_add,map_one,pow_one]
    ring
  have back : integral (-A) 0 F = 0 := by
    rw [show -A=a by exact neg_neg _]
    have zero : integral 0 a F = 0 := paid
    simp only [integral_apply] at zero ⊢
    linarith only [zero]
  rw [negate_interval F A,eq] at back
  let W₁ := c₁*(A^2/2)
  let W₂ := c₂*(A^3/3)
  let W₃ := c₃*(A^4/4)
  let W₄ := c₄*(A^5/5)
  let W₅ := A^6/6
  have w₁ : 0 < W₁ := mul_pos p₁ (div_pos (pow_pos Ap _) (by norm_num))
  have w₂ : 0 < W₂ := mul_pos p₂ (div_pos (pow_pos Ap _) (by norm_num))
  have w₃ : 0 < W₃ := mul_pos p₃ (div_pos (pow_pos Ap _) (by norm_num))
  have w₄ : 0 < W₄ := mul_pos p₄ (div_pos (pow_pos Ap _) (by norm_num))
  have w₅ : 0 < W₅ := div_pos (pow_pos Ap _) (by norm_num)
  have exactMean : W₁*(A*(2/3)-E)+W₂*(A*(3/4)-E)+W₃*(A*(4/5)-E)+
      W₄*(A*(5/6)-E)+W₅*(A*(6/7)-E)=0 := by
    have zero := back
    simp only [V,mul_add,map_add,int_bin] at zero
    norm_num at zero
    dsimp only [W₁,W₂,W₃,W₄,W₅]
    linear_combination zero
  let W := W₁+W₂+W₃+W₄+W₅
  have Wp : 0 < W := add_pos (add_pos (add_pos (add_pos w₁ w₂) w₃) w₄) w₅
  have eqMean : E*W = A*((2/3)*W₁+(3/4)*W₂+(4/5)*W₃+(5/6)*W₄+(6/7)*W₅) := by
    dsimp only [W]
    linear_combination -exactMean
  have low : E*W-((2/3)*A)*W =
      A*(((3/4)-(2/3))*W₂+((4/5)-(2/3))*W₃+((5/6)-(2/3))*W₄+((6/7)-(2/3))*W₅) := by
    rw [eqMean]; dsimp only [W]; ring
  have high : ((6/7)*A)*W-E*W =
      A*(((6/7)-(2/3))*W₁+((6/7)-(3/4))*W₂+((6/7)-(4/5))*W₃+((6/7)-(5/6))*W₄) := by
    rw [eqMean]; dsimp only [W]; ring
  have pl : 0 < E*W-((2/3)*A)*W := by
    rw [low]
    exact mul_pos Ap (add_pos (add_pos (add_pos (mul_pos (by norm_num) w₂)
      (mul_pos (by norm_num) w₃)) (mul_pos (by norm_num) w₄)) (mul_pos (by norm_num) w₅))
  have ph : 0 < ((6/7)*A)*W-E*W := by
    rw [high]
    exact mul_pos Ap (add_pos (add_pos (add_pos (mul_pos (by norm_num) w₁)
      (mul_pos (by norm_num) w₂)) (mul_pos (by norm_num) w₃)) (mul_pos (by norm_num) w₄))
  exact ⟨lt_of_mul_lt_mul_right (sub_pos.mp pl) Wp.le,
    lt_of_mul_lt_mul_right (sub_pos.mp ph) Wp.le⟩

end
end RKCert.ReviewedNative.WeakFiveSoleInner
