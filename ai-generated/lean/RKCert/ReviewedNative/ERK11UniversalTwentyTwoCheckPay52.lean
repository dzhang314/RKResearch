module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay52 : checkBlock payOK Count 52 16 = true := by decide +kernel
theorem checkPay53 : checkBlock payOK Count 53 16 = true := by decide +kernel
theorem checkPay54 : checkBlock payOK Count 54 16 = true := by decide +kernel
theorem checkPay55 : checkBlock payOK Count 55 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
