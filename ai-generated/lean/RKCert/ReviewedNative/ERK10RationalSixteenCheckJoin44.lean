module

public import RKCert.ReviewedNative.ERK10RationalSixteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10RationalSixteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin44 : checkBlock joinOK ActCount 44 4 = true := by decide +kernel
theorem checkJoin45 : checkBlock joinOK ActCount 45 4 = true := by decide +kernel

end RKResearch.Certified.ERK10RationalSixteen
