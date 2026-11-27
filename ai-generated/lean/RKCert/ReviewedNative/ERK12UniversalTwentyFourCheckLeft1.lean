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

def checkLeft1 (k : ℕ) : Bool := matrixBlock (fun i j => leftEntry cov1 i j) (leftScale 1 • left1) k
theorem left1At0 : checkLeft1 0 = true := by decide +kernel
theorem left1At1 : checkLeft1 1 = true := by decide +kernel
theorem left1At2 : checkLeft1 2 = true := by decide +kernel
theorem left1At3 : checkLeft1 3 = true := by decide +kernel
theorem left1At4 : checkLeft1 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
