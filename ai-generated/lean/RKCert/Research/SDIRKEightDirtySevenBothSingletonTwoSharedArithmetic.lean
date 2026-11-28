import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenBothSingletonTwoSharedArithmetic

variable {K : Type*} [CommRing K]

theorem scaled_endpoint_third_difference (l bet f₁ f₂ lam : K) :
    (4*l-bet*lam) - 3*(-2*bet*(f₂+lam*f₁)) +
      3*(-2*bet*(f₁+lam*f₂)) - (4*lam*l-bet) =
      (1-lam)*(4*l+bet*(1+6*(f₂-f₁))) := by
  ring1

theorem affine_fourth_cleared (L A B g c n : K)
    (hL : L = g*(A+B*g)) (hN : c*g = n) :
    c^2*L-A*n*c-B*n^2=0 := by
  rw [hL,←hN]
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenBothSingletonTwoSharedArithmetic
