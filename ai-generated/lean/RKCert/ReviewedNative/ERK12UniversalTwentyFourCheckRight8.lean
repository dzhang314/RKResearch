module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum8

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkRight8 (k : ℕ) : Bool := matrixBlock (fun i j => rightEntry left8 i j) (rightScale 8 • right8) k
theorem right8At0 : checkRight8 0 = true := by decide +kernel
theorem right8At1 : checkRight8 1 = true := by decide +kernel
theorem right8At2 : checkRight8 2 = true := by decide +kernel
theorem right8At3 : checkRight8 3 = true := by decide +kernel
theorem right8At4 : checkRight8 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
