module

public import RKCert.ReviewedNative.ERK10FifteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockJoin16 : block joinOK ActCount 16 8 = true := by decide +kernel

theorem blockJoin17 : block joinOK ActCount 17 8 = true := by decide +kernel

theorem blockJoin18 : block joinOK ActCount 18 8 = true := by decide +kernel

theorem blockJoin19 : block joinOK ActCount 19 8 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF17
