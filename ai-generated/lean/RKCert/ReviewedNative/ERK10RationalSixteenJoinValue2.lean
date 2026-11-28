module

public import RKCert.ReviewedNative.ERK10RationalSixteenJoinSlice2At0
public import RKCert.ReviewedNative.ERK10RationalSixteenJoinSlice2At24
public import RKCert.ReviewedNative.ERK10RationalSixteenJoinSlice2At48

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10RationalSixteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue2 : joinOK (tag 2) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 2)) = 50)
  have H0 := jSlice2At0
  have H1 := glueJoin H0 jSlice2At12
  have H2 := glueJoin H1 jSlice2At24
  have H3 := glueJoin H2 jSlice2At36
  have H4 := glueJoin H3 jSlice2At48
  exact H4


end RKResearch.Certified.ERK10RationalSixteen
