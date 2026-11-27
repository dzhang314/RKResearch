module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay44 : checkBlock payOK Count 44 16 = true := by decide +kernel
theorem checkPay45 : checkBlock payOK Count 45 16 = true := by decide +kernel
theorem checkPay46 : checkBlock payOK Count 46 16 = true := by decide +kernel
theorem checkPay47 : checkBlock payOK Count 47 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
