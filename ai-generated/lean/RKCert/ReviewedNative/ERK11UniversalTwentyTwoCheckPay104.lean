module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay104 : checkBlock payOK Count 104 16 = true := by decide +kernel
theorem checkPay105 : checkBlock payOK Count 105 16 = true := by decide +kernel
theorem checkPay106 : checkBlock payOK Count 106 16 = true := by decide +kernel
theorem checkPay107 : checkBlock payOK Count 107 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
