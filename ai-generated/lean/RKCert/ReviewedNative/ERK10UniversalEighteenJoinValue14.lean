module

public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice14At0

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue14 : joinOK (tag 14) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 14)) = 16)
  have H0 := jSlice14At0
  have H1 := glueJoin H0 jSlice14At12
  exact H1


end RKResearch.Certified.ERK10UniversalEighteen
