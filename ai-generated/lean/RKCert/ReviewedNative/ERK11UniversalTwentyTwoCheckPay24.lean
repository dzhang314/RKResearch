module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay24 : checkBlock payOK Count 24 16 = true := by decide +kernel
theorem checkPay25 : checkBlock payOK Count 25 16 = true := by decide +kernel
theorem checkPay26 : checkBlock payOK Count 26 16 = true := by decide +kernel
theorem checkPay27 : checkBlock payOK Count 27 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
