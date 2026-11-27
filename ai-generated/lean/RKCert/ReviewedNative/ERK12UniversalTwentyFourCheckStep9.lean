module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum9

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkStep9 (k : ℕ) : Bool := matrixBlock (lhs 9 • cov10) (factoredStep 9) k
theorem step9At0 : checkStep9 0 = true := by decide +kernel
theorem step9At1 : checkStep9 1 = true := by decide +kernel
theorem step9At2 : checkStep9 2 = true := by decide +kernel
theorem step9At3 : checkStep9 3 = true := by decide +kernel
theorem step9At4 : checkStep9 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
