/-! Scalar receipts for the neighboring singleton right initial reduction. -/
namespace RKResearch.ERK11NeighborRightInitialGate
open Lean.Grind

theorem rankOneDerivativeBlock {R : Type} [CommRing R]
    (c₀ c₁ k₀₁ k₁₀ k₁₁ : R)
    (ha : c₀+c₁*k₁₀=0) (hb : c₀*k₀₁+c₁*k₁₁=0) :
    c₁*(k₁₁-k₁₀*k₀₁)=0 := by
  calc
    c₁*(k₁₁-k₁₀*k₀₁)=(c₀*k₀₁+c₁*k₁₁)-(c₀+c₁*k₁₀)*k₀₁ := by grind
    _=0 := by rw [ha,hb]; grind

theorem twoRightCalibrations {R : Type} [CommRing R]
    (κ pe qe ps qs fe fs : R)
    (he : κ*qe=fe*pe) (hs : κ*qs=fs*ps) :
    fe*pe*qs-fs*ps*qe=0 := by
  rw [← he,← hs]
  grind

theorem rotatedCurveWitness :
    (1*14+7*(14+14) : Int) % 19 = 1 := by
  decide

theorem fourthCalibrationWitness :
    (5*39*17-37*11*9 : Int) % 41 = 21 := by
  decide

end RKResearch.ERK11NeighborRightInitialGate
#print axioms RKResearch.ERK11NeighborRightInitialGate.rankOneDerivativeBlock
#print axioms RKResearch.ERK11NeighborRightInitialGate.twoRightCalibrations
#print axioms RKResearch.ERK11NeighborRightInitialGate.rotatedCurveWitness
#print axioms RKResearch.ERK11NeighborRightInitialGate.fourthCalibrationWitness
