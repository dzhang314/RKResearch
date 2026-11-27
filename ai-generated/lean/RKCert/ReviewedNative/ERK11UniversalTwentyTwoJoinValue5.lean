module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice5At0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice5At20
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice5At40
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice5At60

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue5 : joinOK (tag 5) = true := by
  apply finishJoin (by decide +kernel : cut (11-grade (tag 5)) = 67)
  have H0 := jSlice5At0
  have H1 := glueJoin H0 jSlice5At10
  have H2 := glueJoin H1 jSlice5At20
  have H3 := glueJoin H2 jSlice5At30
  have H4 := glueJoin H3 jSlice5At40
  have H5 := glueJoin H4 jSlice5At50
  have H6 := glueJoin H5 jSlice5At60
  exact H6


end RKResearch.Certified.ERK11UniversalTwentyTwo
