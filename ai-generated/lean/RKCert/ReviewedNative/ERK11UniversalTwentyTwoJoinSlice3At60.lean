module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice3At60 : joinSlice (tag 3) 60 10 = true := by decide +kernel
theorem jSlice3At70 : joinSlice (tag 3) 70 10 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
