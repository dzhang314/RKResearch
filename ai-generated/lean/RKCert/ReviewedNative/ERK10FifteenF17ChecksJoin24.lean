module

public import RKCert.ReviewedNative.ERK10FifteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockJoin24 : block joinOK ActCount 24 8 = true := by decide +kernel

theorem blockJoin25 : block joinOK ActCount 25 8 = true := by decide +kernel

theorem blockJoin26 : block joinOK ActCount 26 8 = true := by decide +kernel

theorem blockJoin27 : block joinOK ActCount 27 8 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF17
