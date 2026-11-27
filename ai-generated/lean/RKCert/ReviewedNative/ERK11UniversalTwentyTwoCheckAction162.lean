module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction162 : checkBlock actOK ActCount 162 4 = true := by decide +kernel
theorem checkAction163 : checkBlock actOK ActCount 163 4 = true := by decide +kernel
theorem checkAction164 : checkBlock actOK ActCount 164 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
