module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin4 : checkBlock joinOK ActCount 4 4 = true := by decide +kernel
theorem checkJoin5 : checkBlock joinOK ActCount 5 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
