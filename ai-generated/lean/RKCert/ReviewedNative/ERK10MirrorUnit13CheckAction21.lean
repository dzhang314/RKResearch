module

public import RKCert.ReviewedNative.ERK10MirrorUnit13Core

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorUnit13

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkAction21 : checkBlock actOK ActCount 21 4 = true := by decide +kernel
theorem checkAction22 : checkBlock actOK ActCount 22 4 = true := by decide +kernel
theorem checkAction23 : checkBlock actOK ActCount 23 4 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorUnit13
