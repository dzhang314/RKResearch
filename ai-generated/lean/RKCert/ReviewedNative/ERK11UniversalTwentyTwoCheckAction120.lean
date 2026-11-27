module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction120 : checkBlock actOK ActCount 120 4 = true := by decide +kernel
theorem checkAction121 : checkBlock actOK ActCount 121 4 = true := by decide +kernel
theorem checkAction122 : checkBlock actOK ActCount 122 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
