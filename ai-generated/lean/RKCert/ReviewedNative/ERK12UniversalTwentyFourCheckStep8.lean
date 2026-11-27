module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum8

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkStep8 (k : ℕ) : Bool := matrixBlock (lhs 8 • cov9) (factoredStep 8) k
theorem step8At0 : checkStep8 0 = true := by decide +kernel
theorem step8At1 : checkStep8 1 = true := by decide +kernel
theorem step8At2 : checkStep8 2 = true := by decide +kernel
theorem step8At3 : checkStep8 3 = true := by decide +kernel
theorem step8At4 : checkStep8 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
