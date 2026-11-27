module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum4

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkStep4 (k : ℕ) : Bool := matrixBlock (lhs 4 • cov5) (factoredStep 4) k
theorem step4At0 : checkStep4 0 = true := by decide +kernel
theorem step4At1 : checkStep4 1 = true := by decide +kernel
theorem step4At2 : checkStep4 2 = true := by decide +kernel
theorem step4At3 : checkStep4 3 = true := by decide +kernel
theorem step4At4 : checkStep4 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
