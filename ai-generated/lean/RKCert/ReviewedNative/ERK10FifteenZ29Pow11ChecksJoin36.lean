module

public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenZ29Pow11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockJoin36 : block joinOK ActCount 36 8 = true := by decide +kernel

theorem blockJoin37 : block joinOK ActCount 37 8 = true := by decide +kernel

theorem blockJoin38 : block joinOK ActCount 38 8 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenZ29Pow11
