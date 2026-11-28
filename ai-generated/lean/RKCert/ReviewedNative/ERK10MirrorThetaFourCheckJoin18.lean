module

public import RKCert.ReviewedNative.ERK10MirrorThetaFourCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorThetaFour

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin18 : checkBlock joinOK ActCount 18 4 = true := by decide +kernel
theorem checkJoin19 : checkBlock joinOK ActCount 19 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorThetaFour
