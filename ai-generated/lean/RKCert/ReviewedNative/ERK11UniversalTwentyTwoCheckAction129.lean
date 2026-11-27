module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction129 : checkBlock actOK ActCount 129 4 = true := by decide +kernel
theorem checkAction130 : checkBlock actOK ActCount 130 4 = true := by decide +kernel
theorem checkAction131 : checkBlock actOK ActCount 131 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
