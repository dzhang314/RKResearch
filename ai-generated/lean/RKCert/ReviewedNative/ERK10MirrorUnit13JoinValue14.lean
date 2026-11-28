module

public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinSlice14At0

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorUnit13

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue14 : joinOK (tag 14) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 14)) = 7)
  have H0 := jSlice14At0
  exact H0


end RKResearch.Certified.ERK10MirrorUnit13
