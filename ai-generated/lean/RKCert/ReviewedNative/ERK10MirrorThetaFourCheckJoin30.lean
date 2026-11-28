module

public import RKCert.ReviewedNative.ERK10MirrorThetaFourCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorThetaFour

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin30 : checkBlock joinOK ActCount 30 4 = true := by decide +kernel
theorem checkJoin31 : checkBlock joinOK ActCount 31 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorThetaFour
