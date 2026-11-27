module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay60 : checkBlock payOK Count 60 16 = true := by decide +kernel
theorem checkPay61 : checkBlock payOK Count 61 16 = true := by decide +kernel
theorem checkPay62 : checkBlock payOK Count 62 16 = true := by decide +kernel
theorem checkPay63 : checkBlock payOK Count 63 16 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
