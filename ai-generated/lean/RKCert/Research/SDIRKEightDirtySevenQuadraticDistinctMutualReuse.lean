import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticDistinctMutualReuse

variable {R : Type*} [CommRing R]

theorem mutual_reuse_mixed_product (h : R) :
    ((1+4*h-4*h^2)*(-2+h+4*h^2-h^3)+4*h^2*(3*h-2)) -
      (1+2*(2*h)-(2*h)^2)*(-2+h+4*h^2-h^3) =
        4*h^2*(3*h-2) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticDistinctMutualReuse
