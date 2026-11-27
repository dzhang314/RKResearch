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

def checkLeft6 (k : ℕ) : Bool := matrixBlock (fun i j => leftEntry cov6 i j) (leftScale 6 • left6) k
theorem left6At0 : checkLeft6 0 = true := by decide +kernel
theorem left6At1 : checkLeft6 1 = true := by decide +kernel
theorem left6At2 : checkLeft6 2 = true := by decide +kernel
theorem left6At3 : checkLeft6 3 = true := by decide +kernel
theorem left6At4 : checkLeft6 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
