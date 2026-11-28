module

public import RKCert.ReviewedNative.ERK10RationalSixteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10RationalSixteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction18 : checkBlock actOK ActCount 18 4 = true := by decide +kernel
theorem checkAction19 : checkBlock actOK ActCount 19 4 = true := by decide +kernel
theorem checkAction20 : checkBlock actOK ActCount 20 4 = true := by decide +kernel

end RKResearch.Certified.ERK10RationalSixteen
