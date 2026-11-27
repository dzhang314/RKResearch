module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At20
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At40
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At60
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At80
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At100
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At120
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At140
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At160
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At180
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At200
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At220
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At240
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At260
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At280
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At300
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice1At320

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue1 : joinOK (tag 1) = true := by
  apply finishJoin (by decide +kernel : cut (11-grade (tag 1)) = 327)
  have H0 := jSlice1At0
  have H1 := glueJoin H0 jSlice1At10
  have H2 := glueJoin H1 jSlice1At20
  have H3 := glueJoin H2 jSlice1At30
  have H4 := glueJoin H3 jSlice1At40
  have H5 := glueJoin H4 jSlice1At50
  have H6 := glueJoin H5 jSlice1At60
  have H7 := glueJoin H6 jSlice1At70
  have H8 := glueJoin H7 jSlice1At80
  have H9 := glueJoin H8 jSlice1At90
  have H10 := glueJoin H9 jSlice1At100
  have H11 := glueJoin H10 jSlice1At110
  have H12 := glueJoin H11 jSlice1At120
  have H13 := glueJoin H12 jSlice1At130
  have H14 := glueJoin H13 jSlice1At140
  have H15 := glueJoin H14 jSlice1At150
  have H16 := glueJoin H15 jSlice1At160
  have H17 := glueJoin H16 jSlice1At170
  have H18 := glueJoin H17 jSlice1At180
  have H19 := glueJoin H18 jSlice1At190
  have H20 := glueJoin H19 jSlice1At200
  have H21 := glueJoin H20 jSlice1At210
  have H22 := glueJoin H21 jSlice1At220
  have H23 := glueJoin H22 jSlice1At230
  have H24 := glueJoin H23 jSlice1At240
  have H25 := glueJoin H24 jSlice1At250
  have H26 := glueJoin H25 jSlice1At260
  have H27 := glueJoin H26 jSlice1At270
  have H28 := glueJoin H27 jSlice1At280
  have H29 := glueJoin H28 jSlice1At290
  have H30 := glueJoin H29 jSlice1At300
  have H31 := glueJoin H30 jSlice1At310
  have H32 := glueJoin H31 jSlice1At320
  exact H32


end RKResearch.Certified.ERK11UniversalTwentyTwo
