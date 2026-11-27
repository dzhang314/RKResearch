module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum0

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkRight0 (k : ℕ) : Bool := matrixBlock (fun i j => rightEntry left0 i j) (rightScale 0 • right0) k
theorem right0At0 : checkRight0 0 = true := by decide +kernel
theorem right0At1 : checkRight0 1 = true := by decide +kernel
theorem right0At2 : checkRight0 2 = true := by decide +kernel
theorem right0At3 : checkRight0 3 = true := by decide +kernel
theorem right0At4 : checkRight0 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
