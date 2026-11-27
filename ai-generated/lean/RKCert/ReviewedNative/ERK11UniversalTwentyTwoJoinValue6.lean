module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice6At0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice6At20
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice6At40
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinSlice6At60

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem joinValue6 : joinOK (tag 6) = true := by
  apply finishJoin (by decide +kernel : cut (11-grade (tag 6)) = 67)
  have H0 := jSlice6At0
  have H1 := glueJoin H0 jSlice6At10
  have H2 := glueJoin H1 jSlice6At20
  have H3 := glueJoin H2 jSlice6At30
  have H4 := glueJoin H3 jSlice6At40
  have H5 := glueJoin H4 jSlice6At50
  have H6 := glueJoin H5 jSlice6At60
  exact H6


end RKResearch.Certified.ERK11UniversalTwentyTwo
