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

def checkLeft7 (k : ℕ) : Bool := matrixBlock (fun i j => leftEntry cov7 i j) (leftScale 7 • left7) k
theorem left7At0 : checkLeft7 0 = true := by decide +kernel
theorem left7At1 : checkLeft7 1 = true := by decide +kernel
theorem left7At2 : checkLeft7 2 = true := by decide +kernel
theorem left7At3 : checkLeft7 3 = true := by decide +kernel
theorem left7At4 : checkLeft7 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
