module

public import RKCert.ReviewedNative.ERK10UniversalEighteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction78 : checkBlock actOK ActCount 78 4 = true := by decide +kernel
theorem checkAction79 : checkBlock actOK ActCount 79 4 = true := by decide +kernel
theorem checkAction80 : checkBlock actOK ActCount 80 4 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalEighteen
