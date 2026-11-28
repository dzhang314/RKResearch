module

public import RKCert.ReviewedNative.ERK10MirrorUnit13Core
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue0
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue1
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue2
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue3
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue4
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue5
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue6
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue7

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorUnit13

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin0 : checkBlock joinOK ActCount 0 4 = true := by
  change ([tag 0, tag 1, tag 2, tag 3].all joinOK) = true
  simp only [List.all_cons, List.all_nil, Bool.and_self, joinValue0, joinValue1, joinValue2, joinValue3]
theorem checkJoin1 : checkBlock joinOK ActCount 1 4 = true := by
  change ([tag 4, tag 5, tag 6, tag 7].all joinOK) = true
  simp only [List.all_cons, List.all_nil, Bool.and_self, joinValue4, joinValue5, joinValue6, joinValue7]

end RKResearch.Certified.ERK10MirrorUnit13
