module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum6

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkRight6 (k : ℕ) : Bool := matrixBlock (fun i j => rightEntry left6 i j) (rightScale 6 • right6) k
theorem right6At0 : checkRight6 0 = true := by decide +kernel
theorem right6At1 : checkRight6 1 = true := by decide +kernel
theorem right6At2 : checkRight6 2 = true := by decide +kernel
theorem right6At3 : checkRight6 3 = true := by decide +kernel
theorem right6At4 : checkRight6 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
