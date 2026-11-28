module

public import RKCert.ReviewedNative.ERK10MirrorCompactCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorCompact

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin12 : checkBlock joinOK ActCount 12 4 = true := by decide +kernel
theorem checkJoin13 : checkBlock joinOK ActCount 13 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorCompact
