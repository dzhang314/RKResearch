module

public import RKCert.ReviewedNative.ERK10UniversalNineteenJoinSlice1At0
public import RKCert.ReviewedNative.ERK10UniversalNineteenJoinSlice1At24
public import RKCert.ReviewedNative.ERK10UniversalNineteenJoinSlice1At48
public import RKCert.ReviewedNative.ERK10UniversalNineteenJoinSlice1At72
public import RKCert.ReviewedNative.ERK10UniversalNineteenJoinSlice1At96
public import RKCert.ReviewedNative.ERK10UniversalNineteenJoinSlice1At120

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalNineteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue1 : joinOK (tag 1) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 1)) = 132)
  have H0 := jSlice1At0
  have H1 := glueJoin H0 jSlice1At12
  have H2 := glueJoin H1 jSlice1At24
  have H3 := glueJoin H2 jSlice1At36
  have H4 := glueJoin H3 jSlice1At48
  have H5 := glueJoin H4 jSlice1At60
  have H6 := glueJoin H5 jSlice1At72
  have H7 := glueJoin H6 jSlice1At84
  have H8 := glueJoin H7 jSlice1At96
  have H9 := glueJoin H8 jSlice1At108
  have H10 := glueJoin H9 jSlice1At120
  exact H10


end RKResearch.Certified.ERK10UniversalNineteen
