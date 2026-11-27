module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice4At40 : joinSlice (tag 4) 40 10 = true := by decide +kernel
theorem jSlice4At50 : joinSlice (tag 4) 50 10 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
