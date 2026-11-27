module

public import RKCert.ReviewedNative.ERK10UniversalNineteenJoinSlice9At0

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalNineteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue9 : joinOK (tag 9) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 9)) = 16)
  have H0 := jSlice9At0
  have H1 := glueJoin H0 jSlice9At12
  exact H1


end RKResearch.Certified.ERK10UniversalNineteen
