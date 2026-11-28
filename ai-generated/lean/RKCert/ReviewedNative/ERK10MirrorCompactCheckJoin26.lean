module

public import RKCert.ReviewedNative.ERK10MirrorCompactCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorCompact

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin26 : checkBlock joinOK ActCount 26 4 = true := by decide +kernel
theorem checkJoin27 : checkBlock joinOK ActCount 27 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorCompact
