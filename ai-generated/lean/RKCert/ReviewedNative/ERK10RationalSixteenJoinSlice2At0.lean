module

public import RKCert.ReviewedNative.ERK10RationalSixteenJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10RationalSixteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice2At0 : joinSlice (tag 2) 0 12 = true := by decide +kernel
theorem jSlice2At12 : joinSlice (tag 2) 12 12 = true := by decide +kernel

end RKResearch.Certified.ERK10RationalSixteen
