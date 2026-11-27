module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice8At0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice8At20

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue8 : joinOK (tag 8) = true := by
  apply finishJoin (by decide +kernel : cut (11-grade (tag 8)) = 32)
  have H0 := jSlice8At0
  have H1 := glueJoin H0 jSlice8At10
  have H2 := glueJoin H1 jSlice8At20
  have H3 := glueJoin H2 jSlice8At30
  exact H3


end RKResearch.Certified.ERK11UniversalTwentyTwo
