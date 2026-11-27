module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice5At20 : joinSlice (tag 5) 20 10 = true := by decide +kernel
theorem jSlice5At30 : joinSlice (tag 5) 30 10 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
