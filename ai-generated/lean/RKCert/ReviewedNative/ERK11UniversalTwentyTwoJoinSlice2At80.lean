module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice2At80 : joinSlice (tag 2) 80 10 = true := by decide +kernel
theorem jSlice2At90 : joinSlice (tag 2) 90 10 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
