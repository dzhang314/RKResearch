module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction165 : checkBlock actOK ActCount 165 4 = true := by decide +kernel
theorem checkAction166 : checkBlock actOK ActCount 166 4 = true := by decide +kernel
theorem checkAction167 : checkBlock actOK ActCount 167 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
