module

public import RKCert.ReviewedNative.ERK9RationalFifteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9RationalFifteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin4 : checkBlock joinOK ActCount 4 8 = true := by decide +kernel
theorem checkJoin5 : checkBlock joinOK ActCount 5 8 = true := by decide +kernel
theorem checkJoin6 : checkBlock joinOK ActCount 6 8 = true := by decide +kernel
theorem checkJoin7 : checkBlock joinOK ActCount 7 8 = true := by decide +kernel

end RKResearch.Certified.ERK9RationalFifteen
