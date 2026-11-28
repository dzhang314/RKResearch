module

public import RKCert.ReviewedNative.ERK10SixteenF11Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join6At0 : joinSlice (tag 6) 0 24 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF11
