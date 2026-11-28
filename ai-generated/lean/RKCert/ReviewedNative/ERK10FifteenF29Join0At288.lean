module

public import RKCert.ReviewedNative.ERK10FifteenF29Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join0At288 : joinSlice (tag 0) 288 22 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF29
