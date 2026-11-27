module

public import RKCert.ReviewedNative.ERK9RationalFourteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9RationalFourteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin16 : checkBlock joinOK ActCount 16 8 = true := by decide +kernel

end RKResearch.Certified.ERK9RationalFourteen
