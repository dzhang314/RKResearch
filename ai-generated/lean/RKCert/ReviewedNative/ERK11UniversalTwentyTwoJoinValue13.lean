module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice13At0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice13At20

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue13 : joinOK (tag 13) = true := by
  apply finishJoin (by decide +kernel : cut (11-grade (tag 13)) = 32)
  have H0 := jSlice13At0
  have H1 := glueJoin H0 jSlice13At10
  have H2 := glueJoin H1 jSlice13At20
  have H3 := glueJoin H2 jSlice13At30
  exact H3


end RKResearch.Certified.ERK11UniversalTwentyTwo
