/-! Exact scalar checks for the two neighboring K-curve right moment exits. -/
namespace RKResearch.ERK11NeighborKRightMomentArithmetic
open Lean.Grind

theorem restoredMarker : (14*24+12*(9+24) : Int) % 29 = 7 := by
  decide

theorem fallbackAffine : (18+6*16 : Int) % 19 = 0 ∧ (6 : Int) % 19 ≠ 0 := by
  decide

theorem rightCalibrationRemainder {R : Type} [CommRing R] (x : R) :
    16*(14+5*x+x^2+11*x^3+18*x^4) -
      (12+6*x)*x^2*(16-x) -
      16*(18+3*x+5*x^2+x^3)*(16+16*x) -
      16*(11+11*x+13*x^2) =
      19*(-240-288*x-128*x^2-76*x^3+2*x^4) := by
  grind

end RKResearch.ERK11NeighborKRightMomentArithmetic
#print axioms RKResearch.ERK11NeighborKRightMomentArithmetic.restoredMarker
#print axioms RKResearch.ERK11NeighborKRightMomentArithmetic.fallbackAffine
#print axioms RKResearch.ERK11NeighborKRightMomentArithmetic.rightCalibrationRemainder
