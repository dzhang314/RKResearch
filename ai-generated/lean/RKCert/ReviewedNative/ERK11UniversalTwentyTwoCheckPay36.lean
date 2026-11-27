module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay36 : checkBlock payOK Count 36 16 = true := by decide +kernel
theorem checkPay37 : checkBlock payOK Count 37 16 = true := by decide +kernel
theorem checkPay38 : checkBlock payOK Count 38 16 = true := by decide +kernel
theorem checkPay39 : checkBlock payOK Count 39 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
