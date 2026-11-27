module

public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice8At0 : joinSlice (tag 8) 0 12 = true := by decide +kernel
theorem jSlice8At12 : joinSlice (tag 8) 12 4 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalEighteen
