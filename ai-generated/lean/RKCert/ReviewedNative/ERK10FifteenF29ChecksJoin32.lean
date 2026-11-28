module

public import RKCert.ReviewedNative.ERK10FifteenF29Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockJoin32 : block joinOK ActCount 32 8 = true := by decide +kernel

theorem blockJoin33 : block joinOK ActCount 33 8 = true := by decide +kernel

theorem blockJoin34 : block joinOK ActCount 34 8 = true := by decide +kernel

theorem blockJoin35 : block joinOK ActCount 35 8 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF29
