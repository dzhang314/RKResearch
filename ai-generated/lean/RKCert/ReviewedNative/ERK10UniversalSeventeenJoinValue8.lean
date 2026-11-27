module

public import RKCert.ReviewedNative.ERK10UniversalSeventeenJoinSlice8At0

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalSeventeen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue8 : joinOK (tag 8) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 8)) = 16)
  have H0 := jSlice8At0
  have H1 := glueJoin H0 jSlice8At12
  exact H1


end RKResearch.Certified.ERK10UniversalSeventeen
