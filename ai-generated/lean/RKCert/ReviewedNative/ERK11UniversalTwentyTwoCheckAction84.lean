module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction84 : checkBlock actOK ActCount 84 4 = true := by decide +kernel
theorem checkAction85 : checkBlock actOK ActCount 85 4 = true := by decide +kernel
theorem checkAction86 : checkBlock actOK ActCount 86 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
