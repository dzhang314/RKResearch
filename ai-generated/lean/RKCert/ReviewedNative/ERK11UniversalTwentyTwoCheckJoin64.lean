module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin64 : checkBlock joinOK ActCount 64 4 = true := by decide +kernel
theorem checkJoin65 : checkBlock joinOK ActCount 65 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
