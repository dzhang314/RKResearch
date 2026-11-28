module

public import RKCert.ReviewedNative.ERK10MirrorThetaFourCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorThetaFour

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction51 : checkBlock actOK ActCount 51 4 = true := by decide +kernel
theorem checkAction52 : checkBlock actOK ActCount 52 4 = true := by decide +kernel
theorem checkAction53 : checkBlock actOK ActCount 53 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorThetaFour
