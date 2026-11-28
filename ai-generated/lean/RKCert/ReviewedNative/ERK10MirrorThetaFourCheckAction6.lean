module

public import RKCert.ReviewedNative.ERK10MirrorThetaFourCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorThetaFour

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction6 : checkBlock actOK ActCount 6 4 = true := by decide +kernel
theorem checkAction7 : checkBlock actOK ActCount 7 4 = true := by decide +kernel
theorem checkAction8 : checkBlock actOK ActCount 8 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorThetaFour
