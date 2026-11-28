import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticDistinctMixed

variable {R : Type*} [CommRing R]

theorem quadratic_reverse_clock_mask (h v b c : R) :
    ((h-v)^2+b*(h-v)+c)-((h-2*v)^2+b*(h-2*v)+c) =
      v*(2*h+b-3*v) := by
  ring1

theorem quadratic_reverse_ratio_clear (h v b c : R) :
    ((1+4*v-4*v^2)*(-2+v+4*v^2-v^3)+4*v^2*(3*v-2))*
       ((h-v)^2+b*(h-v)+c)-
    (1+2*v-v^2)*(-2+v+4*v^2-v^3)*((h-2*v)^2+b*(h-2*v)+c) =
    v*(1+2*v-v^2)*((-2+v+4*v^2-v^3)*(2*h+b-3*v)-
      (v-2)*(3*v-2)*((h-v)^2+b*(h-v)+c)) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticDistinctMixed
