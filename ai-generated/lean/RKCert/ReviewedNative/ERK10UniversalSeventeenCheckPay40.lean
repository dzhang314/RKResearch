module

public import RKCert.ReviewedNative.ERK10UniversalSeventeenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalSeventeen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay40 : checkBlock payOK Count 40 16 = true := by decide +kernel
theorem checkPay41 : checkBlock payOK Count 41 16 = true := by decide +kernel
theorem checkPay42 : checkBlock payOK Count 42 16 = true := by decide +kernel
theorem checkPay43 : checkBlock payOK Count 43 16 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalSeventeen
