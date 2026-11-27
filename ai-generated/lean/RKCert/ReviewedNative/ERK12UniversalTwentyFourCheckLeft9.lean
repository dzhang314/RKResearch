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

def checkLeft9 (k : ℕ) : Bool := matrixBlock (fun i j => leftEntry cov9 i j) (leftScale 9 • left9) k
theorem left9At0 : checkLeft9 0 = true := by decide +kernel
theorem left9At1 : checkLeft9 1 = true := by decide +kernel
theorem left9At2 : checkLeft9 2 = true := by decide +kernel
theorem left9At3 : checkLeft9 3 = true := by decide +kernel
theorem left9At4 : checkLeft9 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
