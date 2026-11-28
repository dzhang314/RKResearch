module

public import RKCert.ReviewedNative.ERK10FifteenF29Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockAct24 : block actOK ActCount 24 10 = true := by decide +kernel

theorem blockAct25 : block actOK ActCount 25 10 = true := by decide +kernel

theorem blockAct26 : block actOK ActCount 26 10 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF29
