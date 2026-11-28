module

public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinSlice3At0
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinSlice3At24
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinSlice3At48

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorUnit13

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue3 : joinOK (tag 3) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 3)) = 50)
  have H0 := jSlice3At0
  have H1 := glueJoin H0 jSlice3At12
  have H2 := glueJoin H1 jSlice3At24
  have H3 := glueJoin H2 jSlice3At36
  have H4 := glueJoin H3 jSlice3At48
  exact H4


end RKResearch.Certified.ERK10MirrorUnit13
