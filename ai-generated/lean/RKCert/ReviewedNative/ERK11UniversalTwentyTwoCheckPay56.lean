module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay56 : checkBlock payOK Count 56 16 = true := by decide +kernel
theorem checkPay57 : checkBlock payOK Count 57 16 = true := by decide +kernel
theorem checkPay58 : checkBlock payOK Count 58 16 = true := by decide +kernel
theorem checkPay59 : checkBlock payOK Count 59 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
