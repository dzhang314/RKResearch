module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay100 : checkBlock payOK Count 100 16 = true := by decide +kernel
theorem checkPay101 : checkBlock payOK Count 101 16 = true := by decide +kernel
theorem checkPay102 : checkBlock payOK Count 102 16 = true := by decide +kernel
theorem checkPay103 : checkBlock payOK Count 103 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
