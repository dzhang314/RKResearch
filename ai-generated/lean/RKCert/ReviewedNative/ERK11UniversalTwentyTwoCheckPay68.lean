module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay68 : checkBlock payOK Count 68 16 = true := by decide +kernel
theorem checkPay69 : checkBlock payOK Count 69 16 = true := by decide +kernel
theorem checkPay70 : checkBlock payOK Count 70 16 = true := by decide +kernel
theorem checkPay71 : checkBlock payOK Count 71 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
