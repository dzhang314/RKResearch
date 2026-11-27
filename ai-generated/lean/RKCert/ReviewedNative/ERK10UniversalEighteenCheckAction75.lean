module

public import RKCert.ReviewedNative.ERK10UniversalEighteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction75 : checkBlock actOK ActCount 75 4 = true := by decide +kernel
theorem checkAction76 : checkBlock actOK ActCount 76 4 = true := by decide +kernel
theorem checkAction77 : checkBlock actOK ActCount 77 4 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalEighteen
