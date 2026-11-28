import Mathlib.Tactic.Ring.Basic

/-! Scalar exact ratio clearing at the variable midpoint obstruction. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticMidpointVsArithmetic

variable {R : Type*} [CommRing R]

theorem quadratic_clock_difference (h v s : R) :
    ((h-v)^2-s)-((h-2*v)^2-s)=v*(2*h-3*v) := by
  ring1

theorem cleared_midpoint_ratio (h v s : R) :
    ((1+4*v-4*v^2)*(-2+v+4*v^2-v^3)+4*v^2*(3*v-2))*((h-v)^2-s) -
      (1+2*v-v^2)*(-2+v+4*v^2-v^3)*((h-2*v)^2-s) =
    v*(1+2*v-v^2)*((-2+v+4*v^2-v^3)*(2*h-3*v) -
      (v-2)*(3*v-2)*((h-v)^2-s)) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticMidpointVsArithmetic
