module

public import RKCert.ReviewedNative.ERK10MirrorCompactCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorCompact

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin14 : checkBlock joinOK ActCount 14 4 = true := by decide +kernel
theorem checkJoin15 : checkBlock joinOK ActCount 15 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorCompact
