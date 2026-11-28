module

public import RKCert.ReviewedNative.ERK10SixteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join1At48 : joinSlice (tag 1) 48 24 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF17
