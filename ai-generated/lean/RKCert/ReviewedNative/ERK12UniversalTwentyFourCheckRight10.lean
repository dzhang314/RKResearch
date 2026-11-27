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

def checkRight10 (k : ℕ) : Bool := matrixBlock (fun i j => rightEntry left10 i j) (rightScale 10 • right10) k
theorem right10At0 : checkRight10 0 = true := by decide +kernel
theorem right10At1 : checkRight10 1 = true := by decide +kernel
theorem right10At2 : checkRight10 2 = true := by decide +kernel
theorem right10At3 : checkRight10 3 = true := by decide +kernel
theorem right10At4 : checkRight10 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
