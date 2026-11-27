module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice2At20 : joinSlice (tag 2) 20 10 = true := by decide +kernel
theorem jSlice2At30 : joinSlice (tag 2) 30 10 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
