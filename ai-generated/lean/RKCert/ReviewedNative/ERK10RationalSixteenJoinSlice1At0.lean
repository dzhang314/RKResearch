module

public import RKCert.ReviewedNative.ERK10RationalSixteenJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10RationalSixteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice1At0 : joinSlice (tag 1) 0 12 = true := by decide +kernel
theorem jSlice1At12 : joinSlice (tag 1) 12 12 = true := by decide +kernel

end RKResearch.Certified.ERK10RationalSixteen
