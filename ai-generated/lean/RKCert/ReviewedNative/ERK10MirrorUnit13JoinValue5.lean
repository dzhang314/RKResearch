module

public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinSlice5At0
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinSlice5At24

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorUnit13

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue5 : joinOK (tag 5) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 5)) = 25)
  have H0 := jSlice5At0
  have H1 := glueJoin H0 jSlice5At12
  have H2 := glueJoin H1 jSlice5At24
  exact H2


end RKResearch.Certified.ERK10MirrorUnit13
