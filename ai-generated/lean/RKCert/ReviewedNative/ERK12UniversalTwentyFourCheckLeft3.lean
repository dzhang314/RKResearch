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

def checkLeft3 (k : ℕ) : Bool := matrixBlock (fun i j => leftEntry cov3 i j) (leftScale 3 • left3) k
theorem left3At0 : checkLeft3 0 = true := by decide +kernel
theorem left3At1 : checkLeft3 1 = true := by decide +kernel
theorem left3At2 : checkLeft3 2 = true := by decide +kernel
theorem left3At3 : checkLeft3 3 = true := by decide +kernel
theorem left3At4 : checkLeft3 4 = true := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
