module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum6

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkStep6 (k : ℕ) : Bool := matrixBlock (lhs 6 • cov7) (factoredStep 6) k
theorem step6At0 : checkStep6 0 = true := by decide +kernel
theorem step6At1 : checkStep6 1 = true := by decide +kernel
theorem step6At2 : checkStep6 2 = true := by decide +kernel
theorem step6At3 : checkStep6 3 = true := by decide +kernel
theorem step6At4 : checkStep6 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
