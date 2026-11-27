module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction168 : checkBlock actOK ActCount 168 4 = true := by decide +kernel
theorem checkAction169 : checkBlock actOK ActCount 169 4 = true := by decide +kernel
theorem checkAction170 : checkBlock actOK ActCount 170 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
