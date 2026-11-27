module

public import RKCert.ReviewedNative.ERK10UniversalEighteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin60 : checkBlock joinOK ActCount 60 4 = true := by decide +kernel
theorem checkJoin61 : checkBlock joinOK ActCount 61 4 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalEighteen
