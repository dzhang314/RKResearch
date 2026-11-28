module

public import RKCert.ReviewedNative.ERK10FifteenF29Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockAct18 : block actOK ActCount 18 10 = true := by decide +kernel

theorem blockAct19 : block actOK ActCount 19 10 = true := by decide +kernel

theorem blockAct20 : block actOK ActCount 20 10 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF29
