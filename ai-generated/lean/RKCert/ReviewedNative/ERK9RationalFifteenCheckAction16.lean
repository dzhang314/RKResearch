module

public import RKCert.ReviewedNative.ERK9RationalFifteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9RationalFifteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction16 : checkBlock actOK ActCount 16 8 = true := by decide +kernel
theorem checkAction17 : checkBlock actOK ActCount 17 8 = true := by decide +kernel
theorem checkAction18 : checkBlock actOK ActCount 18 8 = true := by decide +kernel

end RKResearch.Certified.ERK9RationalFifteen
