module

public import RKCert.ReviewedNative.ERK10UniversalNineteenJoinSlice13At0

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalNineteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue13 : joinOK (tag 13) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 13)) = 16)
  have H0 := jSlice13At0
  have H1 := glueJoin H0 jSlice13At12
  exact H1


end RKResearch.Certified.ERK10UniversalNineteen
