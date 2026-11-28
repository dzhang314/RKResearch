module

public import RKCert.ReviewedNative.ERK10FifteenF29Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockJoin20 : block joinOK ActCount 20 8 = true := by decide +kernel

theorem blockJoin21 : block joinOK ActCount 21 8 = true := by decide +kernel

theorem blockJoin22 : block joinOK ActCount 22 8 = true := by decide +kernel

theorem blockJoin23 : block joinOK ActCount 23 8 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF29
