module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice0At500 : joinSlice (tag 0) 500 10 = true := by decide +kernel
theorem jSlice0At510 : joinSlice (tag 0) 510 10 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
