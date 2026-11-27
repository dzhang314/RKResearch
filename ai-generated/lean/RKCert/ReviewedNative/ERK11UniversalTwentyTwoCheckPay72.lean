module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay72 : checkBlock payOK Count 72 16 = true := by decide +kernel
theorem checkPay73 : checkBlock payOK Count 73 16 = true := by decide +kernel
theorem checkPay74 : checkBlock payOK Count 74 16 = true := by decide +kernel
theorem checkPay75 : checkBlock payOK Count 75 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
