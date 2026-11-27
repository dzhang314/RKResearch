module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction24 : checkBlock actOK ActCount 24 4 = true := by decide +kernel
theorem checkAction25 : checkBlock actOK ActCount 25 4 = true := by decide +kernel
theorem checkAction26 : checkBlock actOK ActCount 26 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
