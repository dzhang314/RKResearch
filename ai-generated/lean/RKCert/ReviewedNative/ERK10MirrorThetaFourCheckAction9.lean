module

public import RKCert.ReviewedNative.ERK10MirrorThetaFourCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorThetaFour

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction9 : checkBlock actOK ActCount 9 4 = true := by decide +kernel
theorem checkAction10 : checkBlock actOK ActCount 10 4 = true := by decide +kernel
theorem checkAction11 : checkBlock actOK ActCount 11 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorThetaFour
