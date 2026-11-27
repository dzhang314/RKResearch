module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum0

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkStep0 (k : ℕ) : Bool := matrixBlock (lhs 0 • cov1) (factoredStep 0) k
theorem step0At0 : checkStep0 0 = true := by decide +kernel
theorem step0At1 : checkStep0 1 = true := by decide +kernel
theorem step0At2 : checkStep0 2 = true := by decide +kernel
theorem step0At3 : checkStep0 3 = true := by decide +kernel
theorem step0At4 : checkStep0 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
