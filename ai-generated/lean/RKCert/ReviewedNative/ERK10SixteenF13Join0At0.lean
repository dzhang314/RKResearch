module

public import RKCert.ReviewedNative.ERK10SixteenF13Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF13

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join0At0 : joinSlice (tag 0) 0 24 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF13
