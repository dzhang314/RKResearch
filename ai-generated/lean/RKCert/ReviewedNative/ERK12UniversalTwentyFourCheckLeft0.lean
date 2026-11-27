module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore
public import RKCert.ReviewedNative.ERK12UniversalTwentyFourDatum0

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

def checkLeft0 (k : ℕ) : Bool := matrixBlock (fun i j => leftEntry cov0 i j) (leftScale 0 • left0) k
theorem left0At0 : checkLeft0 0 = true := by decide +kernel
theorem left0At1 : checkLeft0 1 = true := by decide +kernel
theorem left0At2 : checkLeft0 2 = true := by decide +kernel
theorem left0At3 : checkLeft0 3 = true := by decide +kernel
theorem left0At4 : checkLeft0 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
