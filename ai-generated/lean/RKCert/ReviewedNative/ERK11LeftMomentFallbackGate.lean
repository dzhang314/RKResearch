/-! Portable scalar checks for the left fixed-moment fallback. -/
namespace RKResearch.ERK11LeftMomentFallbackGate
open Lean.Grind

theorem recoverOuterAffineProduct {R : Type} [CommRing R]
    (p q x a e b₁ s₀ s₁ t : R)
    (h : p*x*(x-a)*e*(t*b₁)+q*(s₀+t*s₁)=0) :
    q*s₀+t*(p*x*(x-a)*e*b₁+q*s₁)=0 := by
  calc
    q*s₀+t*(p*x*(x-a)*e*b₁+q*s₁) =
      p*x*(x-a)*e*(t*b₁)+q*(s₀+t*s₁) := by grind
    _ = 0 := h

theorem clearedCalibrationResidue {R : Type} [CommRing R] (x : R) :
    5*(14+6*x+16*x^2+12*x^3+10*x^4) -
        (16+7*x)*x^2*(5-x) -
        5*(3+9*x+6*x^2+x^3)*(1+8*x) -
        5*(11+7*x+7*x^2) =
      17*(-10*x-25*x^2-12*x^3+x^4) := by
  grind

end RKResearch.ERK11LeftMomentFallbackGate
#print axioms RKResearch.ERK11LeftMomentFallbackGate.recoverOuterAffineProduct
#print axioms RKResearch.ERK11LeftMomentFallbackGate.clearedCalibrationResidue
