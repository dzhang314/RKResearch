import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticFinalBothD

variable {R : Type*} [CommRing R]

/-- Coefficient of t in the product of the two actual adjacent-node
quadratics after t² is replaced by s. -/
theorem even_nodal_linear_coefficient (h s u v : R) :
    (3*v-2*h)*(s+(u-h)*(2*u-h))-(3*u-2*h)*(s+(v-h)*(2*v-h)) =
      (v-u)*(3*s-3*h^2+4*h*(u+v)-6*u*v) := by
  ring1

/-- Polynomial form of the forward singleton ratio, before cancelling
the nonzero literal u and κ. -/
theorem forward_ratio_clear (h u b c : R) :
    ((1+4*u-4*u^2)*(-2+u+4*u^2-u^3)+4*u^2*(3*u-2))*
        ((u-h)^2+b*(u-h)+c)-
      (1+2*u-u^2)*(-2+u+4*u^2-u^3)*((2*u-h)^2+b*(2*u-h)+c) =
    u*(1+2*u-u^2)*((-2+u+4*u^2-u^3)*(2*h-b-3*u)-
      (u-2)*(3*u-2)*((u-h)^2+b*(u-h)+c)) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticFinalBothD
