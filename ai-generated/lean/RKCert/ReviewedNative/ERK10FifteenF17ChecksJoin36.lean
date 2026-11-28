module

public import RKCert.ReviewedNative.ERK10FifteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockJoin36 : block joinOK ActCount 36 8 = true := by decide +kernel

theorem blockJoin37 : block joinOK ActCount 37 8 = true := by decide +kernel

theorem blockJoin38 : block joinOK ActCount 38 8 = true := by decide +kernel

theorem blockJoin39 : block joinOK ActCount 39 8 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF17
