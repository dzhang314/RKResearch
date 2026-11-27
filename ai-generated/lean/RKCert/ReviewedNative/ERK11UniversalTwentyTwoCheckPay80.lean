module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay80 : checkBlock payOK Count 80 16 = true := by decide +kernel
theorem checkPay81 : checkBlock payOK Count 81 16 = true := by decide +kernel
theorem checkPay82 : checkBlock payOK Count 82 16 = true := by decide +kernel
theorem checkPay83 : checkBlock payOK Count 83 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
