module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum2

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkStep2 (k : ℕ) : Bool := matrixBlock (lhs 2 • cov3) (factoredStep 2) k
theorem step2At0 : checkStep2 0 = true := by decide +kernel
theorem step2At1 : checkStep2 1 = true := by decide +kernel
theorem step2At2 : checkStep2 2 = true := by decide +kernel
theorem step2At3 : checkStep2 3 = true := by decide +kernel
theorem step2At4 : checkStep2 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
