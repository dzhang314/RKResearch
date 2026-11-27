module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction42 : checkBlock actOK ActCount 42 4 = true := by decide +kernel
theorem checkAction43 : checkBlock actOK ActCount 43 4 = true := by decide +kernel
theorem checkAction44 : checkBlock actOK ActCount 44 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
