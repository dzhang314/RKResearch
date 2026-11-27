module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction27 : checkBlock actOK ActCount 27 4 = true := by decide +kernel
theorem checkAction28 : checkBlock actOK ActCount 28 4 = true := by decide +kernel
theorem checkAction29 : checkBlock actOK ActCount 29 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
