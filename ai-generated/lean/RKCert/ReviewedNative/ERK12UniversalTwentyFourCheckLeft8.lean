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

def checkLeft8 (k : ℕ) : Bool := matrixBlock (fun i j => leftEntry cov8 i j) (leftScale 8 • left8) k
theorem left8At0 : checkLeft8 0 = true := by decide +kernel
theorem left8At1 : checkLeft8 1 = true := by decide +kernel
theorem left8At2 : checkLeft8 2 = true := by decide +kernel
theorem left8At3 : checkLeft8 3 = true := by decide +kernel
theorem left8At4 : checkLeft8 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
