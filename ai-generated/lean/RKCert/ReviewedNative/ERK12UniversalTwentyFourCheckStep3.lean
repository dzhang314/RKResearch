module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum3

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkStep3 (k : ℕ) : Bool := matrixBlock (lhs 3 • cov4) (factoredStep 3) k
theorem step3At0 : checkStep3 0 = true := by decide +kernel
theorem step3At1 : checkStep3 1 = true := by decide +kernel
theorem step3At2 : checkStep3 2 = true := by decide +kernel
theorem step3At3 : checkStep3 3 = true := by decide +kernel
theorem step3At4 : checkStep3 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
