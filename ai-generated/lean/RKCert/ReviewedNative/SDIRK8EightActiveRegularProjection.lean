module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveRegularProjection

/-- Homogeneous elimination in the centered star square. This identity
also holds when either leading coefficient is zero. -/
theorem homogeneousQuadratic {R : Type*} [CommRing R]
    (a b v q₀ q₁ q₂ : R) (hₐ : a+b*v=0) (hᵩ : q₀+q₁*v+q₂*v^2=0) :
    q₀*b^2-q₁*a*b+q₂*a^2=0 := by
  have ha : a=-(b*v) := by linear_combination hₐ
  rw [ha]
  linear_combination b^2*hᵩ

/-- Fourth-degree nodal projection uses the same cleared identity,
without a unit assumption on the centered tail coefficient. -/
theorem homogeneousQuartic {R : Type*} [CommRing R]
    (a b v q₀ q₁ q₂ q₃ q₄ : R) (hₐ : a+b*v=0)
    (hᵩ : q₀+q₁*v+q₂*v^2+q₃*v^3+q₄*v^4=0) :
    q₀*b^4-q₁*a*b^3+q₂*a^2*b^2-q₃*a^3*b+q₄*a^4=0 := by
  have ha : a=-(b*v) := by linear_combination hₐ
  rw [ha]
  linear_combination b^4*hᵩ

/-- The true arithmetic eighth and penultimate contact equations give the
homogeneous tail relation after multiplying by the terminal clock gap. -/
theorem arithmeticRearCross {R : Type*} [CommRing R]
    (x c d z k H J hx hc hd : R)
    (hdclock : d=2*c-x)
    (h₉ : (x-z)*hc=k*(c-z)*hx)
    (h₈ : H*(x-z)*hd+k*J*(d-z)*hx=0) :
    (x-z)*(H*hd+2*J*hc-k*J*hx)=0 := by
  rw [hdclock] at h₈
  linear_combination h₈+2*J*h₉

#print axioms homogeneousQuadratic
#print axioms homogeneousQuartic
#print axioms arithmeticRearCross

end RKCert.ReviewedNative.SDIRK8EightActiveRegularProjection
