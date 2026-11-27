module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction63 : checkBlock actOK ActCount 63 4 = true := by decide +kernel
theorem checkAction64 : checkBlock actOK ActCount 64 4 = true := by decide +kernel
theorem checkAction65 : checkBlock actOK ActCount 65 4 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
