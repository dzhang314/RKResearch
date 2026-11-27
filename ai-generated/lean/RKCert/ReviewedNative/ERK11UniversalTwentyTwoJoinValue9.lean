module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice9At0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice9At20

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue9 : joinOK (tag 9) = true := by
  apply finishJoin (by decide +kernel : cut (11-grade (tag 9)) = 32)
  have H0 := jSlice9At0
  have H1 := glueJoin H0 jSlice9At10
  have H2 := glueJoin H1 jSlice9At20
  have H3 := glueJoin H2 jSlice9At30
  exact H3


end RKResearch.Certified.ERK11UniversalTwentyTwo
