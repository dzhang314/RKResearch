module

public import RKCert.ReviewedNative.ERK10FifteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockAct30 : block actOK ActCount 30 10 = true := by decide +kernel

theorem blockAct31 : block actOK ActCount 31 10 = true := by decide +kernel

theorem blockAct32 : block actOK ActCount 32 10 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF17
