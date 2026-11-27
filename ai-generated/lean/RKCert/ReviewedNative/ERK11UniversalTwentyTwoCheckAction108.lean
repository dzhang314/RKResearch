module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction108 : checkBlock actOK ActCount 108 4 = true := by decide +kernel
theorem checkAction109 : checkBlock actOK ActCount 109 4 = true := by decide +kernel
theorem checkAction110 : checkBlock actOK ActCount 110 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
