module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin62 : checkBlock joinOK ActCount 62 4 = true := by decide +kernel
theorem checkJoin63 : checkBlock joinOK ActCount 63 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
