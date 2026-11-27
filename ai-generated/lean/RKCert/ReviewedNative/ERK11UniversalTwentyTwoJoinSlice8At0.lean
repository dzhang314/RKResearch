module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice8At0 : joinSlice (tag 8) 0 10 = true := by decide +kernel
theorem jSlice8At10 : joinSlice (tag 8) 10 10 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
