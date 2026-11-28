module

public import RKCert.ReviewedNative.ERK10MirrorCompactJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorCompact

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice6At0 : joinSlice (tag 6) 0 12 = true := by decide +kernel
theorem jSlice6At12 : joinSlice (tag 6) 12 12 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorCompact
