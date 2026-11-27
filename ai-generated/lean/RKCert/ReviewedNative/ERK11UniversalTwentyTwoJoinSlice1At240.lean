module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice1At240 : joinSlice (tag 1) 240 10 = true := by decide +kernel
theorem jSlice1At250 : joinSlice (tag 1) 250 10 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
