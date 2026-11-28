module

public import RKCert.ReviewedNative.ERK10SixteenF19Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF19

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join2At48 : joinSlice (tag 2) 48 2 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF19
