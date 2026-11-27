module

public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice15At0

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue15 : joinOK (tag 15) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 15)) = 16)
  have H0 := jSlice15At0
  have H1 := glueJoin H0 jSlice15At12
  exact H1


end RKResearch.Certified.ERK10UniversalEighteen
