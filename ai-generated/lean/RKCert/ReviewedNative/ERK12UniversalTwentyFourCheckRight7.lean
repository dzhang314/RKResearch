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

def checkRight7 (k : ℕ) : Bool := matrixBlock (fun i j => rightEntry left7 i j) (rightScale 7 • right7) k
theorem right7At0 : checkRight7 0 = true := by decide +kernel
theorem right7At1 : checkRight7 1 = true := by decide +kernel
theorem right7At2 : checkRight7 2 = true := by decide +kernel
theorem right7At3 : checkRight7 3 = true := by decide +kernel
theorem right7At4 : checkRight7 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
