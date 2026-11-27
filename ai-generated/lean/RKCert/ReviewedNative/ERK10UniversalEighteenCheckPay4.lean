module

public import RKCert.ReviewedNative.ERK10UniversalEighteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay4 : checkBlock payOK Count 4 16 = true := by decide +kernel
theorem checkPay5 : checkBlock payOK Count 5 16 = true := by decide +kernel
theorem checkPay6 : checkBlock payOK Count 6 16 = true := by decide +kernel
theorem checkPay7 : checkBlock payOK Count 7 16 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalEighteen
