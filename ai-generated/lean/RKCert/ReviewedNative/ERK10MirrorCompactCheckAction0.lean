module

public import RKCert.ReviewedNative.ERK10MirrorCompactCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorCompact

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction0 : checkBlock actOK ActCount 0 4 = true := by decide +kernel
theorem checkAction1 : checkBlock actOK ActCount 1 4 = true := by decide +kernel
theorem checkAction2 : checkBlock actOK ActCount 2 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorCompact
