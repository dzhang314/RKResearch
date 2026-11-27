module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction180 : checkBlock actOK ActCount 180 4 = true := by decide +kernel
theorem checkAction181 : checkBlock actOK ActCount 181 4 = true := by decide +kernel
theorem checkAction182 : checkBlock actOK ActCount 182 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
