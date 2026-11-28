module

public import RKCert.ReviewedNative.ERK10SixteenF19Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF19

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join0At48 : joinSlice (tag 0) 48 24 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF19
