module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice3At0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice3At20
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice3At40
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice3At60
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice3At80
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice3At100
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice3At120
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice3At140

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue3 : joinOK (tag 3) = true := by
  apply finishJoin (by decide +kernel : cut (11-grade (tag 3)) = 145)
  have H0 := jSlice3At0
  have H1 := glueJoin H0 jSlice3At10
  have H2 := glueJoin H1 jSlice3At20
  have H3 := glueJoin H2 jSlice3At30
  have H4 := glueJoin H3 jSlice3At40
  have H5 := glueJoin H4 jSlice3At50
  have H6 := glueJoin H5 jSlice3At60
  have H7 := glueJoin H6 jSlice3At70
  have H8 := glueJoin H7 jSlice3At80
  have H9 := glueJoin H8 jSlice3At90
  have H10 := glueJoin H9 jSlice3At100
  have H11 := glueJoin H10 jSlice3At110
  have H12 := glueJoin H11 jSlice3At120
  have H13 := glueJoin H12 jSlice3At130
  have H14 := glueJoin H13 jSlice3At140
  exact H14


end RKResearch.Certified.ERK11UniversalTwentyTwo
