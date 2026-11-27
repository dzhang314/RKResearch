module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum4

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkRight4 (k : ℕ) : Bool := matrixBlock (fun i j => rightEntry left4 i j) (rightScale 4 • right4) k
theorem right4At0 : checkRight4 0 = true := by decide +kernel
theorem right4At1 : checkRight4 1 = true := by decide +kernel
theorem right4At2 : checkRight4 2 = true := by decide +kernel
theorem right4At3 : checkRight4 3 = true := by decide +kernel
theorem right4At4 : checkRight4 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
