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

def checkLeft2 (k : ℕ) : Bool := matrixBlock (fun i j => leftEntry cov2 i j) (leftScale 2 • left2) k
theorem left2At0 : checkLeft2 0 = true := by decide +kernel
theorem left2At1 : checkLeft2 1 = true := by decide +kernel
theorem left2At2 : checkLeft2 2 = true := by decide +kernel
theorem left2At3 : checkLeft2 3 = true := by decide +kernel
theorem left2At4 : checkLeft2 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
