module

public import RKCert.ReviewedNative.ERK10SixteenF23Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF23

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join11At0 : joinSlice (tag 11) 0 13 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF23
