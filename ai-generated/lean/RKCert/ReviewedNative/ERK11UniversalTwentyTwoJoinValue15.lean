module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice15At0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice15At20

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue15 : joinOK (tag 15) = true := by
  apply finishJoin (by decide +kernel : cut (11-grade (tag 15)) = 32)
  have H0 := jSlice15At0
  have H1 := glueJoin H0 jSlice15At10
  have H2 := glueJoin H1 jSlice15At20
  have H3 := glueJoin H2 jSlice15At30
  exact H3


end RKResearch.Certified.ERK11UniversalTwentyTwo
