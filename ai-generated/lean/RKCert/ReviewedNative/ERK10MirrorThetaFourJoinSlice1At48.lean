module

public import RKCert.ReviewedNative.ERK10MirrorThetaFourJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorThetaFour

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice1At48 : joinSlice (tag 1) 48 12 = true := by decide +kernel
theorem jSlice1At60 : joinSlice (tag 1) 60 12 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorThetaFour
