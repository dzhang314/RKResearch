module

public import RKCert.ReviewedNative.ERK10MirrorThetaFourCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorThetaFour

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction12 : checkBlock actOK ActCount 12 4 = true := by decide +kernel
theorem checkAction13 : checkBlock actOK ActCount 13 4 = true := by decide +kernel
theorem checkAction14 : checkBlock actOK ActCount 14 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorThetaFour
