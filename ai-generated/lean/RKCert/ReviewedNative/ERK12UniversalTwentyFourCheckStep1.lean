module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum1

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkStep1 (k : ℕ) : Bool := matrixBlock (lhs 1 • cov2) (factoredStep 1) k
theorem step1At0 : checkStep1 0 = true := by decide +kernel
theorem step1At1 : checkStep1 1 = true := by decide +kernel
theorem step1At2 : checkStep1 2 = true := by decide +kernel
theorem step1At3 : checkStep1 3 = true := by decide +kernel
theorem step1At4 : checkStep1 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
