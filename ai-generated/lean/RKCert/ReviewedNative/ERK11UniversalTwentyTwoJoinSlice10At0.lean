module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice10At0 : joinSlice (tag 10) 0 10 = true := by decide +kernel
theorem jSlice10At10 : joinSlice (tag 10) 10 10 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
