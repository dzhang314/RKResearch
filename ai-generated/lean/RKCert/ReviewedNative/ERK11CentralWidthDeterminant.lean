/-! Division-free formulas for the ERK11 central two-clock coefficient
determinant. Here the scalar primitive identity is an input. -/
namespace RKResearch.ERK11CentralWidthDeterminant
open Lean.Grind

variable {R : Type} [CommRing R]

theorem determinantCentered
    (H J C1 C2 I0 I1 I2 : R) (hJ : J = C1 - C2) :
    let A := H^2 - J*I0
    let B := J*I1 - H*C1
    let C := J*I1 - H*C2
    let D := C1*C2 - J*I2
    4*I0*(A*D-B*C) = J*((I0*J)^2 -
      (2*H*I1-I0*(C1+C2))^2 - 4*A*(I0*I2-I1^2)) := by
  dsimp
  rw [hJ]
  grind

theorem halfWidthQuartic (t : R) :
    3*(33*t^4-22*t^2+5) = 11*(3*t^2-1)^2+4 := by
  grind

end RKResearch.ERK11CentralWidthDeterminant

#print axioms RKResearch.ERK11CentralWidthDeterminant.determinantCentered
#print axioms RKResearch.ERK11CentralWidthDeterminant.halfWidthQuartic
