module

public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice6At0
public import RKCert.ReviewedNative.ERK10UniversalEighteenJoinSlice6At24

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue6 : joinOK (tag 6) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 6)) = 32)
  have H0 := jSlice6At0
  have H1 := glueJoin H0 jSlice6At12
  have H2 := glueJoin H1 jSlice6At24
  exact H2


end RKResearch.Certified.ERK10UniversalEighteen
