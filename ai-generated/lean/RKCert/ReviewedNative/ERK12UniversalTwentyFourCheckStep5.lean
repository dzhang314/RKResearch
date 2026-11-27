module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum5

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkStep5 (k : ℕ) : Bool := matrixBlock (lhs 5 • cov6) (factoredStep 5) k
theorem step5At0 : checkStep5 0 = true := by decide +kernel
theorem step5At1 : checkStep5 1 = true := by decide +kernel
theorem step5At2 : checkStep5 2 = true := by decide +kernel
theorem step5At3 : checkStep5 3 = true := by decide +kernel
theorem step5At4 : checkStep5 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
