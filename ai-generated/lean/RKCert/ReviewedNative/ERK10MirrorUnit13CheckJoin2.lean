module

public import RKCert.ReviewedNative.ERK10MirrorUnit13Core
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue8
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue9
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue10
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue11
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue12
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue13
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue14
public import RKCert.ReviewedNative.ERK10MirrorUnit13JoinValue15

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorUnit13

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin2 : checkBlock joinOK ActCount 2 4 = true := by
  change ([tag 8, tag 9, tag 10, tag 11].all joinOK) = true
  simp only [List.all_cons, List.all_nil, Bool.and_self, joinValue8, joinValue9, joinValue10, joinValue11]
theorem checkJoin3 : checkBlock joinOK ActCount 3 4 = true := by
  change ([tag 12, tag 13, tag 14, tag 15].all joinOK) = true
  simp only [List.all_cons, List.all_nil, Bool.and_self, joinValue12, joinValue13, joinValue14, joinValue15]

end RKResearch.Certified.ERK10MirrorUnit13
