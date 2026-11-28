module

public import RKCert.ReviewedNative.ERK10RationalSixteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10RationalSixteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin36 : checkBlock joinOK ActCount 36 4 = true := by decide +kernel
theorem checkJoin37 : checkBlock joinOK ActCount 37 4 = true := by decide +kernel

end RKResearch.Certified.ERK10RationalSixteen
