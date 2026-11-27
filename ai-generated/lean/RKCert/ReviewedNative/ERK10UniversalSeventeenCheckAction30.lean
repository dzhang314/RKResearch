module

public import RKCert.ReviewedNative.ERK10UniversalSeventeenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalSeventeen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction30 : checkBlock actOK ActCount 30 4 = true := by decide +kernel
theorem checkAction31 : checkBlock actOK ActCount 31 4 = true := by decide +kernel
theorem checkAction32 : checkBlock actOK ActCount 32 4 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalSeventeen
