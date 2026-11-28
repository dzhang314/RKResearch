module

public import RKCert.ReviewedNative.ERK10SixteenF19Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF19

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockJoin12 : block joinOK ActCount 12 8 = true := by decide +kernel

theorem blockJoin13 : block joinOK ActCount 13 8 = true := by decide +kernel

theorem blockJoin14 : block joinOK ActCount 14 8 = true := by decide +kernel

theorem blockJoin15 : block joinOK ActCount 15 8 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF19
