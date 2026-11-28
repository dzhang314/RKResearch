module

public import RKCert.ReviewedNative.ERK10SixteenF19Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF19

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join5At24 : joinSlice (tag 5) 24 1 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF19
