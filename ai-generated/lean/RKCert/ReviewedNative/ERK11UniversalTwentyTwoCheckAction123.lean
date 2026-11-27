module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction123 : checkBlock actOK ActCount 123 4 = true := by decide +kernel
theorem checkAction124 : checkBlock actOK ActCount 124 4 = true := by decide +kernel
theorem checkAction125 : checkBlock actOK ActCount 125 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
