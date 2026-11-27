module

public import RKCert.ReviewedNative.ERK9UniversalFifteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9UniversalFifteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction4 : checkBlock actOK ActCount 4 8 = true := by decide +kernel
theorem checkAction5 : checkBlock actOK ActCount 5 8 = true := by decide +kernel
theorem checkAction6 : checkBlock actOK ActCount 6 8 = true := by decide +kernel
theorem checkAction7 : checkBlock actOK ActCount 7 8 = true := by decide +kernel

end RKResearch.Certified.ERK9UniversalFifteen
