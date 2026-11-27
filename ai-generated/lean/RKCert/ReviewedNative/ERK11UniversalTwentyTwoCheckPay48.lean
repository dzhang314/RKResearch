module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay48 : checkBlock payOK Count 48 16 = true := by decide +kernel
theorem checkPay49 : checkBlock payOK Count 49 16 = true := by decide +kernel
theorem checkPay50 : checkBlock payOK Count 50 16 = true := by decide +kernel
theorem checkPay51 : checkBlock payOK Count 51 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
