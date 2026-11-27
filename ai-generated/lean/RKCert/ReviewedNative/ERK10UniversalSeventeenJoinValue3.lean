module

public import RKCert.ReviewedNative.ERK10UniversalSeventeenJoinSlice3At0
public import RKCert.ReviewedNative.ERK10UniversalSeventeenJoinSlice3At24
public import RKCert.ReviewedNative.ERK10UniversalSeventeenJoinSlice3At48

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalSeventeen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue3 : joinOK (tag 3) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 3)) = 67)
  have H0 := jSlice3At0
  have H1 := glueJoin H0 jSlice3At12
  have H2 := glueJoin H1 jSlice3At24
  have H3 := glueJoin H2 jSlice3At36
  have H4 := glueJoin H3 jSlice3At48
  have H5 := glueJoin H4 jSlice3At60
  exact H5


end RKResearch.Certified.ERK10UniversalSeventeen
