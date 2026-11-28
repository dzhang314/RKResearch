module

public import RKCert.ReviewedNative.ERK10RationalSixteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10RationalSixteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction3 : checkBlock actOK ActCount 3 4 = true := by decide +kernel
theorem checkAction4 : checkBlock actOK ActCount 4 4 = true := by decide +kernel
theorem checkAction5 : checkBlock actOK ActCount 5 4 = true := by decide +kernel

end RKResearch.Certified.ERK10RationalSixteen
