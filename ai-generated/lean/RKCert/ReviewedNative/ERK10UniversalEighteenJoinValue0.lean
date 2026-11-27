module

public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At0
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At24
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At48
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At72
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At96
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At120
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At144
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At168
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At192
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At216
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At240
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At264
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At288
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice0At312

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue0 : joinOK (tag 0) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 0)) = 327)
  have H0 := jSlice0At0
  have H1 := glueJoin H0 jSlice0At12
  have H2 := glueJoin H1 jSlice0At24
  have H3 := glueJoin H2 jSlice0At36
  have H4 := glueJoin H3 jSlice0At48
  have H5 := glueJoin H4 jSlice0At60
  have H6 := glueJoin H5 jSlice0At72
  have H7 := glueJoin H6 jSlice0At84
  have H8 := glueJoin H7 jSlice0At96
  have H9 := glueJoin H8 jSlice0At108
  have H10 := glueJoin H9 jSlice0At120
  have H11 := glueJoin H10 jSlice0At132
  have H12 := glueJoin H11 jSlice0At144
  have H13 := glueJoin H12 jSlice0At156
  have H14 := glueJoin H13 jSlice0At168
  have H15 := glueJoin H14 jSlice0At180
  have H16 := glueJoin H15 jSlice0At192
  have H17 := glueJoin H16 jSlice0At204
  have H18 := glueJoin H17 jSlice0At216
  have H19 := glueJoin H18 jSlice0At228
  have H20 := glueJoin H19 jSlice0At240
  have H21 := glueJoin H20 jSlice0At252
  have H22 := glueJoin H21 jSlice0At264
  have H23 := glueJoin H22 jSlice0At276
  have H24 := glueJoin H23 jSlice0At288
  have H25 := glueJoin H24 jSlice0At300
  have H26 := glueJoin H25 jSlice0At312
  have H27 := glueJoin H26 jSlice0At324
  exact H27


end RKResearch.Certified.ERK10UniversalEighteen
