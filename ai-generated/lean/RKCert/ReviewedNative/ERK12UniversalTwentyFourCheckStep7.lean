module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum7

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkStep7 (k : ℕ) : Bool := matrixBlock (lhs 7 • cov8) (factoredStep 7) k
theorem step7At0 : checkStep7 0 = true := by decide +kernel
theorem step7At1 : checkStep7 1 = true := by decide +kernel
theorem step7At2 : checkStep7 2 = true := by decide +kernel
theorem step7At3 : checkStep7 3 = true := by decide +kernel
theorem step7At4 : checkStep7 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
