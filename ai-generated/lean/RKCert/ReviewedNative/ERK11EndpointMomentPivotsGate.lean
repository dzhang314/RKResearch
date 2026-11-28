/-! Scalar certificates at the endpoint-alias fixed-moment fallback places. -/
namespace RKResearch.ERK11EndpointMomentPivotsGate
open Lean.Grind

theorem restoredRightFirstPoolMark :
    (0*8+1*(8+8) : Int) % 29 = 16 ∧ (16 : Int) % 29 ≠ 0 := by
  decide

theorem restoredBothFirstPoolMark :
    (7*19+18*(22+19) : Int) % 31 = 3 ∧ (3 : Int) % 31 ≠ 0 := by
  decide

theorem clearedRightCalibrationResidue {R : Type} [CommRing R] (y : R) :
    8*(15+17*y+9*y^2+16*y^3+y^4) -
      (11+y)*y^2*(8-y) -
      8*(15+5*y+14*y^2+y^3)*(3+13*y) -
      8*(8+16*y+5*y^2) =
    19*(-16-88*y-48*y^2-71*y^3-5*y^4) := by
  grind

end RKResearch.ERK11EndpointMomentPivotsGate
#print axioms RKResearch.ERK11EndpointMomentPivotsGate.restoredRightFirstPoolMark
#print axioms RKResearch.ERK11EndpointMomentPivotsGate.restoredBothFirstPoolMark
#print axioms RKResearch.ERK11EndpointMomentPivotsGate.clearedRightCalibrationResidue
