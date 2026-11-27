module

public import RKCert.ReviewedNative.ERK12UniversalTwentyFourCore

@[expose] public section

/-! Generated content-factored exact integer Gram certificate. -/

namespace RKResearch.Certified.ERK12UniversalTwentyFour
open RootedTreeGram
open scoped Matrix FiniteRootedTree
set_option maxHeartbeats 0
set_option maxRecDepth 40000
set_option Elab.async false

theorem checkedBase : covScale 0 • cov 0 = outer 1 := by
  apply extOfBlocks
  decide +kernel

theorem energy0 : energy (cov 0) (output w D (0+1)) = 0 := by decide +kernel

theorem energy1 : energy (cov 1) (output w D (1+1)) = 0 := by decide +kernel

theorem energy2 : energy (cov 2) (output w D (2+1)) = 0 := by decide +kernel

theorem energy3 : energy (cov 3) (output w D (3+1)) = 0 := by decide +kernel

theorem energy4 : energy (cov 4) (output w D (4+1)) = 0 := by decide +kernel

theorem energy5 : energy (cov 5) (output w D (5+1)) = 0 := by decide +kernel

theorem energy6 : energy (cov 6) (output w D (6+1)) = 0 := by decide +kernel

theorem energy7 : energy (cov 7) (output w D (7+1)) = 0 := by decide +kernel

theorem energy8 : energy (cov 8) (output w D (8+1)) = 0 := by decide +kernel

theorem energy9 : energy (cov 9) (output w D (9+1)) = 0 := by decide +kernel

theorem energy10 : energy (cov 10) (output w D (10+1)) = 0 := by decide +kernel

theorem energy11 : energy (cov 11) (output w D (11+1)) = 0 := by decide +kernel

end RKResearch.Certified.ERK12UniversalTwentyFour
