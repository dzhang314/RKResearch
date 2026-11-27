module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay92 : checkBlock payOK Count 92 16 = true := by decide +kernel
theorem checkPay93 : checkBlock payOK Count 93 16 = true := by decide +kernel
theorem checkPay94 : checkBlock payOK Count 94 16 = true := by decide +kernel
theorem checkPay95 : checkBlock payOK Count 95 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
