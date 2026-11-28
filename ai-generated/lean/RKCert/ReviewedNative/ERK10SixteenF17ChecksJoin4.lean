module

public import RKCert.ReviewedNative.ERK10SixteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockJoin4 : block joinOK ActCount 4 8 = true := by decide +kernel

theorem blockJoin5 : block joinOK ActCount 5 8 = true := by decide +kernel

theorem blockJoin6 : block joinOK ActCount 6 8 = true := by decide +kernel

theorem blockJoin7 : block joinOK ActCount 7 8 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF17
