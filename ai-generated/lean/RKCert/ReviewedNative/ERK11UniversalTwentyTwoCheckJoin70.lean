module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin70 : checkBlock joinOK ActCount 70 4 = true := by decide +kernel
theorem checkJoin71 : checkBlock joinOK ActCount 71 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
