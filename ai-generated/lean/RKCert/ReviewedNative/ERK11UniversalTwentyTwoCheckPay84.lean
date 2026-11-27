module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay84 : checkBlock payOK Count 84 16 = true := by decide +kernel
theorem checkPay85 : checkBlock payOK Count 85 16 = true := by decide +kernel
theorem checkPay86 : checkBlock payOK Count 86 16 = true := by decide +kernel
theorem checkPay87 : checkBlock payOK Count 87 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
