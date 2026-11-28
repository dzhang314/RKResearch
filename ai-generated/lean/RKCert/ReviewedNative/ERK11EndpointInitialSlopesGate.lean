/-! Scalar actual-slope and finite-place unit checks for the endpoint aliases. -/
namespace RKResearch.ERK11EndpointInitialSlopesGate
open Lean.Grind

theorem secondSlopeZero {K : Type} [Field K]
    (c₀ c₁ s₀ s₁ : K)
    (h : c₀*s₀-c₁*s₁=0) (h₀ : s₀=0) (h₁ : c₁≠0) :
    s₁=0 := by
  rw [h₀] at h
  grind

theorem cubicPlaceBezout {R : Type} [CommRing R] (x : R) :
    (3*x^2+5*x+9)*(2*x^2+15*x+1)+(17*x+3)*(x^3+2*x^2+17*x+5) =
      1+23*(x^4+4*x^3+17*x^2+12*x+1) := by
  grind

end RKResearch.ERK11EndpointInitialSlopesGate
#print axioms RKResearch.ERK11EndpointInitialSlopesGate.secondSlopeZero
#print axioms RKResearch.ERK11EndpointInitialSlopesGate.cubicPlaceBezout
