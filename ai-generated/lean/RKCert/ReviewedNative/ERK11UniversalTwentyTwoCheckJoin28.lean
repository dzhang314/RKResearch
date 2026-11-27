module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin28 : checkBlock joinOK ActCount 28 4 = true := by decide +kernel
theorem checkJoin29 : checkBlock joinOK ActCount 29 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
