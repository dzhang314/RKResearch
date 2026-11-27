module

public import RKCert.ReviewedNative.ERK10UniversalEighteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay8 : checkBlock payOK Count 8 16 = true := by decide +kernel
theorem checkPay9 : checkBlock payOK Count 9 16 = true := by decide +kernel
theorem checkPay10 : checkBlock payOK Count 10 16 = true := by decide +kernel
theorem checkPay11 : checkBlock payOK Count 11 16 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalEighteen
