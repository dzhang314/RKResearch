module

public import RKCert.ReviewedNative.ERK10UniversalEighteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin66 : checkBlock joinOK ActCount 66 4 = true := by decide +kernel
theorem checkJoin67 : checkBlock joinOK ActCount 67 4 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalEighteen
