import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSFrontDssStar

variable {K : Type*} [CommRing K]

theorem star_nodal_component (y s c W₀ : K) :
    y*(y-s) = (y^2-2*c*y+W₀)+((2*c-s)*y-W₀) := by
  ring1

/-- The normalized nodal condition does not divide by the symmetric-gap
or half-amplitude factor. -/
theorem normalized_star_nodal_clear
    (s f c W₀ l₀ l₁ : K)
    (h : (2*f-1)*W₀=s*(s-2*c)) :
    W₀*(s*l₁-(2*f-1)*l₀)=s*(W₀*l₁+(2*c-s)*l₀) := by
  calc
    _ = W₀*s*l₁-((2*f-1)*W₀)*l₀ := by ring1
    _ = _ := by rw [h]; ring1

theorem half_amplitude_arithmetic_factor (u : K) :
    (1+4*u-4*u^2)*(-2+u+4*u^2-u^3)+4*u^2*(3*u-2)
        -(-2+u+4*u^2-u^3) =
      4*u*(u-2)*(u^3-3*u^2+1) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSFrontDssStar
