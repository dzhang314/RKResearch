module

public import RKCert.ReviewedNative.ERK9RationalFifteenSecondCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9RationalFifteenSecond

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction0 : checkBlock actOK ActCount 0 8 = true := by decide +kernel
theorem checkAction1 : checkBlock actOK ActCount 1 8 = true := by decide +kernel
theorem checkAction2 : checkBlock actOK ActCount 2 8 = true := by decide +kernel
theorem checkAction3 : checkBlock actOK ActCount 3 8 = true := by decide +kernel

end RKResearch.Certified.ERK9RationalFifteenSecond
