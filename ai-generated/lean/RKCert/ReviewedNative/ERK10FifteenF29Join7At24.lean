module

public import RKCert.ReviewedNative.ERK10FifteenF29Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join7At24 : joinSlice (tag 7) 24 8 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF29
