module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice7At0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice7At20
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice7At40
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice7At60

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue7 : joinOK (tag 7) = true := by
  apply finishJoin (by decide +kernel : cut (11-grade (tag 7)) = 67)
  have H0 := jSlice7At0
  have H1 := glueJoin H0 jSlice7At10
  have H2 := glueJoin H1 jSlice7At20
  have H3 := glueJoin H2 jSlice7At30
  have H4 := glueJoin H3 jSlice7At40
  have H5 := glueJoin H4 jSlice7At50
  have H6 := glueJoin H5 jSlice7At60
  exact H6


end RKResearch.Certified.ERK11UniversalTwentyTwo
