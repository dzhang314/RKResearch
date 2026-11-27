module

public import RKCert.ReviewedNative.ERK10UniversalSeventeenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalSeventeen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin68 : checkBlock joinOK ActCount 68 4 = true := by decide +kernel
theorem checkJoin69 : checkBlock joinOK ActCount 69 4 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalSeventeen
