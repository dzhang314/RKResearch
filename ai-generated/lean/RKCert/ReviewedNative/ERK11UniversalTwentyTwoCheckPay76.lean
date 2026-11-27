module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay76 : checkBlock payOK Count 76 16 = true := by decide +kernel
theorem checkPay77 : checkBlock payOK Count 77 16 = true := by decide +kernel
theorem checkPay78 : checkBlock payOK Count 78 16 = true := by decide +kernel
theorem checkPay79 : checkBlock payOK Count 79 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
