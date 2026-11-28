import Mathlib.Tactic.Ring.Basic

/-! Scalar parity and graph-root masks for the quadratic doubled-end star chart. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticEndStars

variable {R : Type*} [CommRing R]

theorem squared_root_cross_product (a b : R) :
    (5*b-3)*(35*a^2-30*a+3)-(5*a-3)*(35*b^2-30*b+3) =
      5*(a-b)*(35*a*b-21*a-21*b+15) := by
  ring1

theorem forward_star_endpoint_gap (x s : R) :
    (2-x)*(1-s)-(x-s)=(1-x)*(2-s) := by
  ring1

theorem even_shared_odd_mask (u v s : R) :
    v*(s+2*u^2)-u*(s+2*v^2)=(v-u)*(s-2*u*v) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticEndStars
