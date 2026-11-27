module

public import RKCert.ReviewedNative.ERK10UniversalSeventeenJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalSeventeen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice2At24 : joinSlice (tag 2) 24 12 = true := by decide +kernel
theorem jSlice2At36 : joinSlice (tag 2) 36 12 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalSeventeen
