module

public import RKCert.ReviewedNative.ERK10MirrorThetaFourCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorThetaFour

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay28 : checkBlock payOK Count 28 16 = true := by decide +kernel
theorem checkPay29 : checkBlock payOK Count 29 16 = true := by decide +kernel
theorem checkPay30 : checkBlock payOK Count 30 16 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorThetaFour
