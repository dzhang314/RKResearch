module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay88 : checkBlock payOK Count 88 16 = true := by decide +kernel
theorem checkPay89 : checkBlock payOK Count 89 16 = true := by decide +kernel
theorem checkPay90 : checkBlock payOK Count 90 16 = true := by decide +kernel
theorem checkPay91 : checkBlock payOK Count 91 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
