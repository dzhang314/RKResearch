module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction111 : checkBlock actOK ActCount 111 4 = true := by decide +kernel
theorem checkAction112 : checkBlock actOK ActCount 112 4 = true := by decide +kernel
theorem checkAction113 : checkBlock actOK ActCount 113 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
