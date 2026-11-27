module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction135 : checkBlock actOK ActCount 135 4 = true := by decide +kernel
theorem checkAction136 : checkBlock actOK ActCount 136 4 = true := by decide +kernel
theorem checkAction137 : checkBlock actOK ActCount 137 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
