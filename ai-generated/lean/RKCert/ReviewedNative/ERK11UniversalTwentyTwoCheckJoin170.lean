module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin170 : checkBlock joinOK ActCount 170 4 = true := by decide +kernel
theorem checkJoin171 : checkBlock joinOK ActCount 171 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
