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

def checkRight5 (k : ℕ) : Bool := matrixBlock (fun i j => rightEntry left5 i j) (rightScale 5 • right5) k
theorem right5At0 : checkRight5 0 = true := by decide +kernel
theorem right5At1 : checkRight5 1 = true := by decide +kernel
theorem right5At2 : checkRight5 2 = true := by decide +kernel
theorem right5At3 : checkRight5 3 = true := by decide +kernel
theorem right5At4 : checkRight5 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
