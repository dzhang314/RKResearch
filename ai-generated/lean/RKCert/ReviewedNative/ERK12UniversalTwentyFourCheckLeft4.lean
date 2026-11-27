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

def checkLeft4 (k : ℕ) : Bool := matrixBlock (fun i j => leftEntry cov4 i j) (leftScale 4 • left4) k
theorem left4At0 : checkLeft4 0 = true := by decide +kernel
theorem left4At1 : checkLeft4 1 = true := by decide +kernel
theorem left4At2 : checkLeft4 2 = true := by decide +kernel
theorem left4At3 : checkLeft4 3 = true := by decide +kernel
theorem left4At4 : checkLeft4 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
