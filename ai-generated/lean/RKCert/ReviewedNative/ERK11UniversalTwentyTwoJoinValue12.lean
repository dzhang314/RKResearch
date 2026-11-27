module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice12At0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice12At20

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue12 : joinOK (tag 12) = true := by
  apply finishJoin (by decide +kernel : cut (11-grade (tag 12)) = 32)
  have H0 := jSlice12At0
  have H1 := glueJoin H0 jSlice12At10
  have H2 := glueJoin H1 jSlice12At20
  have H3 := glueJoin H2 jSlice12At30
  exact H3


end RKResearch.Certified.ERK11UniversalTwentyTwo
