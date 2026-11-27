module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction126 : checkBlock actOK ActCount 126 4 = true := by decide +kernel
theorem checkAction127 : checkBlock actOK ActCount 127 4 = true := by decide +kernel
theorem checkAction128 : checkBlock actOK ActCount 128 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
