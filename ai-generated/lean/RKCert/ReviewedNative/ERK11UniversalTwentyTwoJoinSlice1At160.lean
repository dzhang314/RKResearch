module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice1At160 : joinSlice (tag 1) 160 10 = true := by decide +kernel
theorem jSlice1At170 : joinSlice (tag 1) 170 10 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
