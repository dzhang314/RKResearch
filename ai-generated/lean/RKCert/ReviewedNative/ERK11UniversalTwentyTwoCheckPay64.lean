module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay64 : checkBlock payOK Count 64 16 = true := by decide +kernel
theorem checkPay65 : checkBlock payOK Count 65 16 = true := by decide +kernel
theorem checkPay66 : checkBlock payOK Count 66 16 = true := by decide +kernel
theorem checkPay67 : checkBlock payOK Count 67 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
