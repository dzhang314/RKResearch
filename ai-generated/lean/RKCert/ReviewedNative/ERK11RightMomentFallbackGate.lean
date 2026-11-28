/-! Exact scalar arithmetic at the right fixed-moment fallback place. -/
namespace RKResearch.ERK11RightMomentFallbackGate

theorem restoredRightPivot :
    ((9 : Int)*(13*9-4*16)-23*(21*9-4*18)+16*(21*16-13*18)) % 31 = 7 := by
  decide

theorem affineProductResidue :
    (10 + 25*12 : Int) % 31 = 0 ∧ (12 : Int) % 31 ≠ 0 := by
  decide

theorem firstPoolObstruction :
    (28*10+10*(26+10) : Int) % 31 = 20 ∧ (20 : Int) % 31 ≠ 0 := by
  decide

end RKResearch.ERK11RightMomentFallbackGate
#print axioms RKResearch.ERK11RightMomentFallbackGate.restoredRightPivot
#print axioms RKResearch.ERK11RightMomentFallbackGate.affineProductResidue
#print axioms RKResearch.ERK11RightMomentFallbackGate.firstPoolObstruction
