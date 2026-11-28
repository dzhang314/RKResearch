module

public import RKCert.ReviewedNative.ERK10RationalSixteenJoinSlice15At0

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10RationalSixteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue15 : joinOK (tag 15) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 15)) = 7)
  have H0 := jSlice15At0
  exact H0


end RKResearch.Certified.ERK10RationalSixteen
