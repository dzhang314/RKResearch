module

public import RKCert.ReviewedNative.ERK10UniversalNineteenJoinSlice7At0
public import RKCert.ReviewedNative.ERK10UniversalNineteenJoinSlice7At24

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalNineteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue7 : joinOK (tag 7) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 7)) = 32)
  have H0 := jSlice7At0
  have H1 := glueJoin H0 jSlice7At12
  have H2 := glueJoin H1 jSlice7At24
  exact H2


end RKResearch.Certified.ERK10UniversalNineteen
