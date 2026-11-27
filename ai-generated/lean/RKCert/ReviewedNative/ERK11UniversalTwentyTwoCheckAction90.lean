module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction90 : checkBlock actOK ActCount 90 4 = true := by decide +kernel
theorem checkAction91 : checkBlock actOK ActCount 91 4 = true := by decide +kernel
theorem checkAction92 : checkBlock actOK ActCount 92 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
