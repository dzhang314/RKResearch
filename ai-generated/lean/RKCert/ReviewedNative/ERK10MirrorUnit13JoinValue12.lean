module

public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinSlice12At0

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorUnit13

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue12 : joinOK (tag 12) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 12)) = 13)
  have H0 := jSlice12At0
  have H1 := glueJoin H0 jSlice12At12
  exact H1


end RKResearch.Certified.ERK10MirrorUnit13
