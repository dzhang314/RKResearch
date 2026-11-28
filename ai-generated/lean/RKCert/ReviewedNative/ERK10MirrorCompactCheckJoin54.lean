module

public import RKCert.ReviewedNative.ERK10MirrorCompactCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorCompact

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin54 : checkBlock joinOK ActCount 54 4 = true := by decide +kernel
theorem checkJoin55 : checkBlock joinOK ActCount 55 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorCompact
