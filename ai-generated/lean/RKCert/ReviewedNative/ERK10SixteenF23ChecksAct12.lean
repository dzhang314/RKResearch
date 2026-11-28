module

public import RKCert.ReviewedNative.ERK10SixteenF23Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF23

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockAct12 : block actOK ActCount 12 10 = true := by decide +kernel

theorem blockAct13 : block actOK ActCount 13 10 = true := by decide +kernel

theorem blockAct14 : block actOK ActCount 14 10 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF23
