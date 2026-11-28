module

public import RKCert.ReviewedNative.ERK10SixteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockAct9 : block actOK ActCount 9 10 = true := by decide +kernel

theorem blockAct10 : block actOK ActCount 10 10 = true := by decide +kernel

theorem blockAct11 : block actOK ActCount 11 10 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF17
