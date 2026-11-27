module

public import RKCert.ReviewedNative.ERK9UniversalFifteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9UniversalFifteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay12 : checkBlock payOK Count 12 16 = true := by decide +kernel
theorem checkPay13 : checkBlock payOK Count 13 16 = true := by decide +kernel
theorem checkPay14 : checkBlock payOK Count 14 16 = true := by decide +kernel
theorem checkPay15 : checkBlock payOK Count 15 16 = true := by decide +kernel

end RKResearch.Certified.ERK9UniversalFifteen
