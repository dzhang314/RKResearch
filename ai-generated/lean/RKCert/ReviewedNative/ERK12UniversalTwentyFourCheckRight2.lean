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

def checkRight2 (k : ℕ) : Bool := matrixBlock (fun i j => rightEntry left2 i j) (rightScale 2 • right2) k
theorem right2At0 : checkRight2 0 = true := by decide +kernel
theorem right2At1 : checkRight2 1 = true := by decide +kernel
theorem right2At2 : checkRight2 2 = true := by decide +kernel
theorem right2At3 : checkRight2 3 = true := by decide +kernel
theorem right2At4 : checkRight2 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
