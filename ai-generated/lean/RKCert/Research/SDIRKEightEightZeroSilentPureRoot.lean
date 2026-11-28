import Mathlib.Tactic.Ring.Basic

/-! Scalar gates for the simultaneous silent and pure-zero root. -/

namespace RKResearch.Certified.SDIRKEightEightZeroSilentPureRoot

variable {R : Type*} [CommRing R]

/-- Cross-cancel two ordinary primitive errors from a common pure line. -/
theorem cancel_common_line (a b j k : R) :
    (b*j)*(a*k)-(a*j)*(b*k)=0 := by ring1

/-- Three homogeneous rows on a common monic quadratic force a zero
determinant, independently of any possible moment pivot. -/
theorem monic_tail_determinant {a b c d e f g h i x y : R}
    (h₀ : a*x+b*y+c=0) (h₁ : d*x+e*y+f=0)
    (h₂ : g*x+h*y+i=0) :
    a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)=0 := by
  calc
    _ = (d*h-e*g)*(a*x+b*y+c)
        +(b*g-a*h)*(d*x+e*y+f)
        +(a*e-b*d)*(g*x+h*y+i) := by ring1
    _ = 0 := by rw [h₀,h₁,h₂,mul_zero,mul_zero,mul_zero,zero_add,zero_add]

end RKResearch.Certified.SDIRKEightEightZeroSilentPureRoot
