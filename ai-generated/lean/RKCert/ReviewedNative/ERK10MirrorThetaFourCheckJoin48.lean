module

public import RKCert.ReviewedNative.ERK10MirrorThetaFourCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorThetaFour

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin48 : checkBlock joinOK ActCount 48 4 = true := by decide +kernel
theorem checkJoin49 : checkBlock joinOK ActCount 49 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorThetaFour
