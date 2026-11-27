module

public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice1At96 : joinSlice (tag 1) 96 12 = true := by decide +kernel
theorem jSlice1At108 : joinSlice (tag 1) 108 12 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalEighteen
