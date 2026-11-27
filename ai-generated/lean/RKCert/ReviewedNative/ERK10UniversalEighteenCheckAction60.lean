module

public import RKCert.ReviewedNative.ERK10UniversalEighteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction60 : checkBlock actOK ActCount 60 4 = true := by decide +kernel
theorem checkAction61 : checkBlock actOK ActCount 61 4 = true := by decide +kernel
theorem checkAction62 : checkBlock actOK ActCount 62 4 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalEighteen
