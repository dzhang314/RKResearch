module

public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At0
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At24
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At48
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At72
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At96
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At120
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At144
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At168
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At192
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At216
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At240
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At264
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0At288

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenZ29Pow11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join0 : joinOK (tag 0) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 0)) = 310)
  have H0 := join0At0
  have H1 := glueJoin H0 join0At24
  have H2 := glueJoin H1 join0At48
  have H3 := glueJoin H2 join0At72
  have H4 := glueJoin H3 join0At96
  have H5 := glueJoin H4 join0At120
  have H6 := glueJoin H5 join0At144
  have H7 := glueJoin H6 join0At168
  have H8 := glueJoin H7 join0At192
  have H9 := glueJoin H8 join0At216
  have H10 := glueJoin H9 join0At240
  have H11 := glueJoin H10 join0At264
  have H12 := glueJoin H11 join0At288
  exact H12


end RKResearch.Certified.ERK10FifteenZ29Pow11
