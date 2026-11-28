module

public import RKCert.ReviewedNative.ERK10SixteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join12At0 : joinSlice (tag 12) 0 13 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF17
