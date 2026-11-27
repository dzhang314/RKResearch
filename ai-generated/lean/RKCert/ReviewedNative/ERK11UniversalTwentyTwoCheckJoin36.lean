module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin36 : checkBlock joinOK ActCount 36 4 = true := by decide +kernel
theorem checkJoin37 : checkBlock joinOK ActCount 37 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
