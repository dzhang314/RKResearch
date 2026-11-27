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

def checkRight9 (k : ℕ) : Bool := matrixBlock (fun i j => rightEntry left9 i j) (rightScale 9 • right9) k
theorem right9At0 : checkRight9 0 = true := by decide +kernel
theorem right9At1 : checkRight9 1 = true := by decide +kernel
theorem right9At2 : checkRight9 2 = true := by decide +kernel
theorem right9At3 : checkRight9 3 = true := by decide +kernel
theorem right9At4 : checkRight9 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
