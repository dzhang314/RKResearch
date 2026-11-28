module

public import RKCert.ReviewedNative.ERK10FifteenF29Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockAct27 : block actOK ActCount 27 10 = true := by decide +kernel

theorem blockAct28 : block actOK ActCount 28 10 = true := by decide +kernel

theorem blockAct29 : block actOK ActCount 29 10 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF29
