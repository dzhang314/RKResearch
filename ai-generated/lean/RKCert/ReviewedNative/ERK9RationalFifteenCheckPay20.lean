module

public import RKCert.ReviewedNative.ERK9RationalFifteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9RationalFifteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay20 : checkBlock payOK Count 20 16 = true := by decide +kernel

end RKResearch.Certified.ERK9RationalFifteen
