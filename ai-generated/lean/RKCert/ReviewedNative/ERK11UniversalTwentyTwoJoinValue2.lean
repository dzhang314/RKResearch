module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice2At0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice2At20
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice2At40
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice2At60
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice2At80
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice2At100
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice2At120
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice2At140

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue2 : joinOK (tag 2) = true := by
  apply finishJoin (by decide +kernel : cut (11-grade (tag 2)) = 145)
  have H0 := jSlice2At0
  have H1 := glueJoin H0 jSlice2At10
  have H2 := glueJoin H1 jSlice2At20
  have H3 := glueJoin H2 jSlice2At30
  have H4 := glueJoin H3 jSlice2At40
  have H5 := glueJoin H4 jSlice2At50
  have H6 := glueJoin H5 jSlice2At60
  have H7 := glueJoin H6 jSlice2At70
  have H8 := glueJoin H7 jSlice2At80
  have H9 := glueJoin H8 jSlice2At90
  have H10 := glueJoin H9 jSlice2At100
  have H11 := glueJoin H10 jSlice2At110
  have H12 := glueJoin H11 jSlice2At120
  have H13 := glueJoin H12 jSlice2At130
  have H14 := glueJoin H13 jSlice2At140
  exact H14


end RKResearch.Certified.ERK11UniversalTwentyTwo
