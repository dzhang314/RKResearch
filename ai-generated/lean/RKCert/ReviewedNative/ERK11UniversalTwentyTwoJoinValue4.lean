module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice4At0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice4At20
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice4At40
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice4At60

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue4 : joinOK (tag 4) = true := by
  apply finishJoin (by decide +kernel : cut (11-grade (tag 4)) = 67)
  have H0 := jSlice4At0
  have H1 := glueJoin H0 jSlice4At10
  have H2 := glueJoin H1 jSlice4At20
  have H3 := glueJoin H2 jSlice4At30
  have H4 := glueJoin H3 jSlice4At40
  have H5 := glueJoin H4 jSlice4At50
  have H6 := glueJoin H5 jSlice4At60
  exact H6


end RKResearch.Certified.ERK11UniversalTwentyTwo
