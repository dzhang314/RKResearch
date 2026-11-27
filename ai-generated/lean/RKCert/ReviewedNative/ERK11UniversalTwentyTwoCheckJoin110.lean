module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin110 : checkBlock joinOK ActCount 110 4 = true := by decide +kernel
theorem checkJoin111 : checkBlock joinOK ActCount 111 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
