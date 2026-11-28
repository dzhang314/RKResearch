module

public import RKCert.ReviewedNative.ERK10FifteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockJoin8 : block joinOK ActCount 8 8 = true := by decide +kernel

theorem blockJoin9 : block joinOK ActCount 9 8 = true := by decide +kernel

theorem blockJoin10 : block joinOK ActCount 10 8 = true := by decide +kernel

theorem blockJoin11 : block joinOK ActCount 11 8 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF17
