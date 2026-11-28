module

public import RKCert.ReviewedNative.ERK10FifteenF29Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockAct6 : block actOK ActCount 6 10 = true := by decide +kernel

theorem blockAct7 : block actOK ActCount 7 10 = true := by decide +kernel

theorem blockAct8 : block actOK ActCount 8 10 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF29
