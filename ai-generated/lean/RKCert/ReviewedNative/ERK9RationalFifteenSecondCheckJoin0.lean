module

public import RKCert.ReviewedNative.ERK9RationalFifteenSecondCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9RationalFifteenSecond

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin0 : checkBlock joinOK ActCount 0 8 = true := by decide +kernel
theorem checkJoin1 : checkBlock joinOK ActCount 1 8 = true := by decide +kernel
theorem checkJoin2 : checkBlock joinOK ActCount 2 8 = true := by decide +kernel
theorem checkJoin3 : checkBlock joinOK ActCount 3 8 = true := by decide +kernel

end RKResearch.Certified.ERK9RationalFifteenSecond
