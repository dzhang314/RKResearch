module

public import RKCert.ReviewedNative.ERK9RationalFourteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9RationalFourteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin8 : checkBlock joinOK ActCount 8 8 = true := by decide +kernel
theorem checkJoin9 : checkBlock joinOK ActCount 9 8 = true := by decide +kernel
theorem checkJoin10 : checkBlock joinOK ActCount 10 8 = true := by decide +kernel
theorem checkJoin11 : checkBlock joinOK ActCount 11 8 = true := by decide +kernel

end RKResearch.Certified.ERK9RationalFourteen
