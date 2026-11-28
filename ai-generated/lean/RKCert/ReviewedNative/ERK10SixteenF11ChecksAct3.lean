module

public import RKCert.ReviewedNative.ERK10SixteenF11Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockAct3 : block actOK ActCount 3 10 = true := by decide +kernel

theorem blockAct4 : block actOK ActCount 4 10 = true := by decide +kernel

theorem blockAct5 : block actOK ActCount 5 10 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF11
