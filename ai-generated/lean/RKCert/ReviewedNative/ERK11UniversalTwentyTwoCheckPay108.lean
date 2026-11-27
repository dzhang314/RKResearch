module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay108 : checkBlock payOK Count 108 16 = true := by decide +kernel
theorem checkPay109 : checkBlock payOK Count 109 16 = true := by decide +kernel
theorem checkPay110 : checkBlock payOK Count 110 16 = true := by decide +kernel
theorem checkPay111 : checkBlock payOK Count 111 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
