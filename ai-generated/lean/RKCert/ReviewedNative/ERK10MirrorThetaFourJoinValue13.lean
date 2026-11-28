module

public import RKCert.ReviewedNative.ERK10MirrorThetaFourJoinSlice13At0

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorThetaFour

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue13 : joinOK (tag 13) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 13)) = 7)
  have H0 := jSlice13At0
  exact H0


end RKResearch.Certified.ERK10MirrorThetaFour
