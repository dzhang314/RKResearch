module

public import RKCert.ReviewedNative.ERK10SixteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockAct21 : block actOK ActCount 21 10 = true := by decide +kernel

theorem blockAct22 : block actOK ActCount 22 10 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF17
