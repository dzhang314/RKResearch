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

def checkLeft10 (k : ℕ) : Bool := matrixBlock (fun i j => leftEntry cov10 i j) (leftScale 10 • left10) k
theorem left10At0 : checkLeft10 0 = true := by decide +kernel
theorem left10At1 : checkLeft10 1 = true := by decide +kernel
theorem left10At2 : checkLeft10 2 = true := by decide +kernel
theorem left10At3 : checkLeft10 3 = true := by decide +kernel
theorem left10At4 : checkLeft10 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
