module

public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice2At48 : joinSlice (tag 2) 48 12 = true := by decide +kernel
theorem jSlice2At60 : joinSlice (tag 2) 60 7 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalEighteen
