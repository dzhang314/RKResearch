module

public import RKCert.ReviewedNative.ERK10FifteenF29Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join1At0 : joinSlice (tag 1) 0 24 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF29
