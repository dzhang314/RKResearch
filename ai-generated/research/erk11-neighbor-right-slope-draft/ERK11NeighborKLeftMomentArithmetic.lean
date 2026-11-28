/-! Exact scalar checks for the two neighboring K-curve left moment exits. -/
namespace RKResearch.ERK11NeighborKLeftMomentArithmetic
open Lean.Grind

theorem restoredMarker : (17*2+1*(9+2) : Int) % 19 = 7 := by
  decide

theorem fallbackAffine : (2+33*31 : Int) % 41 = 0 ∧ (33 : Int) % 41 ≠ 0 := by
  decide

theorem leftCalibrationRemainder {R : Type} [CommRing R] (x : R) :
    33*(16+19*x+10*x^2+32*x^3+20*x^4) -
      (15+2*x)*x^2*(33-x) -
      33*(2+39*x+29*x^2+x^3)*(14+30*x) -
      33*(29+28*x+18*x^2) =
      41*(-33-495*x-1287*x^2-687*x^3-8*x^4) := by
  grind

end RKResearch.ERK11NeighborKLeftMomentArithmetic
#print axioms RKResearch.ERK11NeighborKLeftMomentArithmetic.restoredMarker
#print axioms RKResearch.ERK11NeighborKLeftMomentArithmetic.fallbackAffine
#print axioms RKResearch.ERK11NeighborKLeftMomentArithmetic.leftCalibrationRemainder
