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

def checkRight1 (k : ℕ) : Bool := matrixBlock (fun i j => rightEntry left1 i j) (rightScale 1 • right1) k
theorem right1At0 : checkRight1 0 = true := by decide +kernel
theorem right1At1 : checkRight1 1 = true := by decide +kernel
theorem right1At2 : checkRight1 2 = true := by decide +kernel
theorem right1At3 : checkRight1 3 = true := by decide +kernel
theorem right1At4 : checkRight1 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
