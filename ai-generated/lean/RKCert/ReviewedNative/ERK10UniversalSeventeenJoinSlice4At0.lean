module

public import RKCert.ReviewedNative.ERK10UniversalSeventeenJoinPoint

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalSeventeen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem jSlice4At0 : joinSlice (tag 4) 0 12 = true := by decide +kernel
theorem jSlice4At12 : joinSlice (tag 4) 12 12 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalSeventeen
