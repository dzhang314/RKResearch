module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction96 : checkBlock actOK ActCount 96 4 = true := by decide +kernel
theorem checkAction97 : checkBlock actOK ActCount 97 4 = true := by decide +kernel
theorem checkAction98 : checkBlock actOK ActCount 98 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
