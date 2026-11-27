module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice2At60 : joinSlice (tag 2) 60 10 = true := by decide +kernel
theorem jSlice2At70 : joinSlice (tag 2) 70 10 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
