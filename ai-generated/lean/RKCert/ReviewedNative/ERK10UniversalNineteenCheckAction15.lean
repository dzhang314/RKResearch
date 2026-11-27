module

public import RKCert.ReviewedNative.ERK10UniversalNineteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalNineteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction15 : checkBlock actOK ActCount 15 4 = true := by decide +kernel
theorem checkAction16 : checkBlock actOK ActCount 16 4 = true := by decide +kernel
theorem checkAction17 : checkBlock actOK ActCount 17 4 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalNineteen
