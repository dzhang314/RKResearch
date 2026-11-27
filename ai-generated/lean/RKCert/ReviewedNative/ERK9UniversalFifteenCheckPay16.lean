module

public import RKCert.ReviewedNative.ERK9UniversalFifteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9UniversalFifteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay16 : checkBlock payOK Count 16 16 = true := by decide +kernel
theorem checkPay17 : checkBlock payOK Count 17 16 = true := by decide +kernel

end RKResearch.Certified.ERK9UniversalFifteen
