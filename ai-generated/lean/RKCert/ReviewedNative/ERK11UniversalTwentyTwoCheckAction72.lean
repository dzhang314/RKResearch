module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction72 : checkBlock actOK ActCount 72 4 = true := by decide +kernel
theorem checkAction73 : checkBlock actOK ActCount 73 4 = true := by decide +kernel
theorem checkAction74 : checkBlock actOK ActCount 74 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
