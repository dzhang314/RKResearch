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

def checkLeft5 (k : ℕ) : Bool := matrixBlock (fun i j => leftEntry cov5 i j) (leftScale 5 • left5) k
theorem left5At0 : checkLeft5 0 = true := by decide +kernel
theorem left5At1 : checkLeft5 1 = true := by decide +kernel
theorem left5At2 : checkLeft5 2 = true := by decide +kernel
theorem left5At3 : checkLeft5 3 = true := by decide +kernel
theorem left5At4 : checkLeft5 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
