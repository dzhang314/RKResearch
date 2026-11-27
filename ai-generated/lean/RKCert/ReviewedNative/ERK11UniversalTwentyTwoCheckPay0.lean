module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay0 : checkBlock payOK Count 0 16 = true := by decide +kernel
theorem checkPay1 : checkBlock payOK Count 1 16 = true := by decide +kernel
theorem checkPay2 : checkBlock payOK Count 2 16 = true := by decide +kernel
theorem checkPay3 : checkBlock payOK Count 3 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
