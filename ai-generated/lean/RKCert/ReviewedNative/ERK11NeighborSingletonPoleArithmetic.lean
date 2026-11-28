/-! Core scalar receipts for the neighboring singleton diagonal-pole exit. -/
namespace RKResearch.ERK11NeighborSingletonPoleArithmetic
open Lean.Grind

theorem smallWidthOne {R : Type} [CommRing R] (a : R) :
    48*(12*a^2-9*a+2)=(24*a-9)^2+15 := by
  grind

theorem smallWidthTwo {R : Type} [CommRing R] (a : R) :
    220*(55*a^2-33*a+6)=(110*a-33)^2+231 := by
  grind

theorem rightCalibrationResidue {R : Type} [CommRing R] (y : R) :
    5*(11+9*y+25*y^2+12*y^3+2*y^4) -
      (13+2*y)*y^2*(5-y) -
      5*(25+4*y+26*y^2+y^3)*(6+21*y) -
      5*(16+18*y+20*y^2) =
      31*(-25-90*y-40*y^2-87*y^3-3*y^4) := by
  grind

theorem pairResidueOne {R : Type} [CommRing R] (u : R) :
    ((4*u+4)-12*(7*u+26))^2 -
      ((7*u+26)-12*(25*u+1))*((9*u+12)-12*(4*u+4)) =
    (23*u+8)-5027*(u^2+23*u+24)+31*(4996*u+6968) := by
  grind

theorem pairResidueTwo {R : Type} [CommRing R] (u : R) :
    ((24*u+1)-12*(2*u+4))^2 -
      ((2*u+4)-12*(17*u+1))*((26*u+6)-12*(24*u+1)) =
    (16*u+3)-52924*(u^2+u+15)+31*(1600*u+25678) := by
  grind

theorem pairResidueThree {R : Type} [CommRing R] (u : R) :
    (20-12*(18*u+26))^2 -
      ((18*u+26)-12*(5*u+7))*((22*u+8)-12*20) =
    (30*u+23)+47580*(u^2+6*u+27)+31*(-5414*u-39125) := by
  grind

end RKResearch.ERK11NeighborSingletonPoleArithmetic
#print axioms RKResearch.ERK11NeighborSingletonPoleArithmetic.smallWidthOne
#print axioms RKResearch.ERK11NeighborSingletonPoleArithmetic.smallWidthTwo
#print axioms RKResearch.ERK11NeighborSingletonPoleArithmetic.rightCalibrationResidue
#print axioms RKResearch.ERK11NeighborSingletonPoleArithmetic.pairResidueOne
#print axioms RKResearch.ERK11NeighborSingletonPoleArithmetic.pairResidueTwo
#print axioms RKResearch.ERK11NeighborSingletonPoleArithmetic.pairResidueThree
