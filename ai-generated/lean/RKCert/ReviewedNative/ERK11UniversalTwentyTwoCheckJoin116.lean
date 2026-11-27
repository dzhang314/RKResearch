module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin116 : checkBlock joinOK ActCount 116 4 = true := by decide +kernel
theorem checkJoin117 : checkBlock joinOK ActCount 117 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
