module

public import RKCert.ReviewedNative.ERK10FifteenF17Join1At0
public import RKCert.ReviewedNative.ERK10FifteenF17Join1At24
public import RKCert.ReviewedNative.ERK10FifteenF17Join1At48
public import RKCert.ReviewedNative.ERK10FifteenF17Join1At72
public import RKCert.ReviewedNative.ERK10FifteenF17Join1At96
public import RKCert.ReviewedNative.ERK10FifteenF17Join1At120
public import RKCert.ReviewedNative.ERK10FifteenF17Join1At144

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join1 : joinOK (tag 1) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 1)) = 145)
  have H0 := join1At0
  have H1 := glueJoin H0 join1At24
  have H2 := glueJoin H1 join1At48
  have H3 := glueJoin H2 join1At72
  have H4 := glueJoin H3 join1At96
  have H5 := glueJoin H4 join1At120
  have H6 := glueJoin H5 join1At144
  exact H6


end RKResearch.Certified.ERK10FifteenF17
