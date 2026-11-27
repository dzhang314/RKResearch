module

public import RKCert.ReviewedNative.ERK9UniversalFifteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9UniversalFifteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin12 : checkBlock joinOK ActCount 12 8 = true := by decide +kernel
theorem checkJoin13 : checkBlock joinOK ActCount 13 8 = true := by decide +kernel
theorem checkJoin14 : checkBlock joinOK ActCount 14 8 = true := by decide +kernel
theorem checkJoin15 : checkBlock joinOK ActCount 15 8 = true := by decide +kernel

end RKResearch.Certified.ERK9UniversalFifteen
