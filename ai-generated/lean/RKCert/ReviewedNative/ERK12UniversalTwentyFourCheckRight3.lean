module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum3

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkRight3 (k : ℕ) : Bool := matrixBlock (fun i j => rightEntry left3 i j) (rightScale 3 • right3) k
theorem right3At0 : checkRight3 0 = true := by decide +kernel
theorem right3At1 : checkRight3 1 = true := by decide +kernel
theorem right3At2 : checkRight3 2 = true := by decide +kernel
theorem right3At3 : checkRight3 3 = true := by decide +kernel
theorem right3At4 : checkRight3 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
