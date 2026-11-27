module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum10

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkStep10 (k : ℕ) : Bool := matrixBlock (lhs 10 • cov11) (factoredStep 10) k
theorem step10At0 : checkStep10 0 = true := by decide +kernel
theorem step10At1 : checkStep10 1 = true := by decide +kernel
theorem step10At2 : checkStep10 2 = true := by decide +kernel
theorem step10At3 : checkStep10 3 = true := by decide +kernel
theorem step10At4 : checkStep10 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
