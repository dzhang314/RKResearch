module

public import RKCert.ReviewedNative.ERK10MirrorCompactJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorCompact

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice3At24 : joinSlice (tag 3) 24 12 = true := by decide +kernel
theorem jSlice3At36 : joinSlice (tag 3) 36 12 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorCompact
