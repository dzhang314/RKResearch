module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay96 : checkBlock payOK Count 96 16 = true := by decide +kernel
theorem checkPay97 : checkBlock payOK Count 97 16 = true := by decide +kernel
theorem checkPay98 : checkBlock payOK Count 98 16 = true := by decide +kernel
theorem checkPay99 : checkBlock payOK Count 99 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
