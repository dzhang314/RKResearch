module

public import RKCert.ReviewedNative.ERK10RationalSixteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10RationalSixteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin16 : checkBlock joinOK ActCount 16 4 = true := by decide +kernel
theorem checkJoin17 : checkBlock joinOK ActCount 17 4 = true := by decide +kernel

end RKResearch.Certified.ERK10RationalSixteen
