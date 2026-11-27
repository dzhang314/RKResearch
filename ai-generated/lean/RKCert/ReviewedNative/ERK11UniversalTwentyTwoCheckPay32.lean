module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay32 : checkBlock payOK Count 32 16 = true := by decide +kernel
theorem checkPay33 : checkBlock payOK Count 33 16 = true := by decide +kernel
theorem checkPay34 : checkBlock payOK Count 34 16 = true := by decide +kernel
theorem checkPay35 : checkBlock payOK Count 35 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
