module

public import RKCert.ReviewedNative.ERK10FifteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockJoin28 : block joinOK ActCount 28 8 = true := by decide +kernel

theorem blockJoin29 : block joinOK ActCount 29 8 = true := by decide +kernel

theorem blockJoin30 : block joinOK ActCount 30 8 = true := by decide +kernel

theorem blockJoin31 : block joinOK ActCount 31 8 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF17
