module

public import RKCert.ReviewedNative.ERK10UniversalNineteenJoinSlice10At0

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalNineteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue10 : joinOK (tag 10) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 10)) = 16)
  have H0 := jSlice10At0
  have H1 := glueJoin H0 jSlice10At12
  exact H1


end RKResearch.Certified.ERK10UniversalNineteen
