module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

/-! Scalar gates for the first distinct clock in the five-degree decoder floor.
The actual-prefix rank and chronology argument is recorded separately. -/

namespace RKResearch.Certified.DIRKDenseFiveScalar

variable {K : Type*} [Field K] [CharZero K]

theorem no_clean_self (z r : K) (hz : z≠0)
    (h₁ : r*z=z^2/2) (h₂ : r*z^2=z^3/3) : False := by
  have e : z^3/2=z^3/3 := calc
    _ = (z^2/2)*z := by ring
    _ = (r*z)*z := by rw [h₁]
    _ = r*z^2 := by ring
    _ = _ := h₂
  have he : z^3=0 := calc
    _ = (6:K)*(z^3/2-z^3/3) := by ring
    _ = 0 := by rw [e,sub_self,mul_zero]
  exact pow_ne_zero 3 hz he

theorem defect_relation (z t : K) :
    z^2*t-z^3/3 = z*(z*t-z^2/2)+z^3/6 := by ring

theorem same_amplitude (z μ d₁ d₂ : K) (hz : z≠0)
    (h₁ : μ*d₁=z*d₁+z^3/6) (h₂ : μ*d₂=z*d₂+z^3/6) :
    d₁=d₂ ∧ d₁≠0 := by
  have e₁ : (μ-z)*d₁=z^3/6 := by rw [sub_mul,h₁,add_sub_cancel_left]
  have e₂ : (μ-z)*d₂=z^3/6 := by rw [sub_mul,h₂,add_sub_cancel_left]
  have hunit : z^3/6≠0 := div_ne_zero (pow_ne_zero 3 hz) (by norm_num)
  have hn : μ-z≠0 := by
    intro h
    rw [h,zero_mul] at e₁
    exact hunit e₁.symm
  refine ⟨mul_left_cancel₀ hn (e₁.trans e₂.symm),?_⟩
  intro h
  rw [h,mul_zero] at e₁
  exact hunit e₁.symm

theorem amplitude_C2 (z t : K) (h : z*t=z^2/2) :
    z^2*t-z^3/3=z^3/6 := by
  rw [defect_relation z t,h,sub_self,mul_zero,zero_add]

#print axioms no_clean_self
#print axioms same_amplitude
#print axioms amplitude_C2

end RKResearch.Certified.DIRKDenseFiveScalar
