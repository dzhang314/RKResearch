module

public import RKCert.ReviewedNative.ERK10SixteenF13Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF13

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockAct0 : block actOK ActCount 0 10 = true := by decide +kernel

theorem blockAct1 : block actOK ActCount 1 10 = true := by decide +kernel

theorem blockAct2 : block actOK ActCount 2 10 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF13
