module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction102 : checkBlock actOK ActCount 102 4 = true := by decide +kernel
theorem checkAction103 : checkBlock actOK ActCount 103 4 = true := by decide +kernel
theorem checkAction104 : checkBlock actOK ActCount 104 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
