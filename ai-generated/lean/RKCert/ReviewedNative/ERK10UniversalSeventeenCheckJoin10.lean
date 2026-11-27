module

public import RKCert.ReviewedNative.ERK10UniversalSeventeenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalSeventeen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin10 : checkBlock joinOK ActCount 10 4 = true := by decide +kernel
theorem checkJoin11 : checkBlock joinOK ActCount 11 4 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalSeventeen
