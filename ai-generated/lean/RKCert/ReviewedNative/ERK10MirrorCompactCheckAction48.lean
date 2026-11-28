module

public import RKCert.ReviewedNative.ERK10MirrorCompactCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorCompact

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction48 : checkBlock actOK ActCount 48 4 = true := by decide +kernel
theorem checkAction49 : checkBlock actOK ActCount 49 4 = true := by decide +kernel
theorem checkAction50 : checkBlock actOK ActCount 50 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorCompact
