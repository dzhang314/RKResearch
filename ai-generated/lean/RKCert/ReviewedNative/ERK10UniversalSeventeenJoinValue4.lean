module

public import RKCert.ReviewedNative.ERK10UniversalSeventeenJoinSlice4At0
public import RKCert.ReviewedNative.ERK10UniversalSeventeenJoinSlice4At24

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalSeventeen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue4 : joinOK (tag 4) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 4)) = 32)
  have H0 := jSlice4At0
  have H1 := glueJoin H0 jSlice4At12
  have H2 := glueJoin H1 jSlice4At24
  exact H2


end RKResearch.Certified.ERK10UniversalSeventeen
