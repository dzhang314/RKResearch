module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinValue0
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinValue1
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinValue2
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinValue3
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinValue4
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinValue5
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinValue6
public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoJoinValue7

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkJoin0 : checkBlock joinOK ActCount 0 4 = true := by
  change ([tag 0, tag 1, tag 2, tag 3].all joinOK) = true
  simp only [List.all_cons, List.all_nil, Bool.and_self, joinValue0, joinValue1, joinValue2, joinValue3]
theorem checkJoin1 : checkBlock joinOK ActCount 1 4 = true := by
  change ([tag 4, tag 5, tag 6, tag 7].all joinOK) = true
  simp only [List.all_cons, List.all_nil, Bool.and_self, joinValue4, joinValue5, joinValue6, joinValue7]

end RKResearch.Certified.ERK11UniversalTwentyTwo
