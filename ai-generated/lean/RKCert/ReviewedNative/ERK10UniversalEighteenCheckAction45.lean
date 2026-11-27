module

public import RKCert.ReviewedNative.ERK10UniversalEighteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction45 : checkBlock actOK ActCount 45 4 = true := by decide +kernel
theorem checkAction46 : checkBlock actOK ActCount 46 4 = true := by decide +kernel
theorem checkAction47 : checkBlock actOK ActCount 47 4 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalEighteen
