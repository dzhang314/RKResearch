module

public import RKCert.ReviewedNative.ERK10UniversalSeventeenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalSeventeen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin76 : checkBlock joinOK ActCount 76 4 = true := by decide +kernel
theorem checkJoin77 : checkBlock joinOK ActCount 77 4 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalSeventeen
