module

public import RKCert.ReviewedNative.ERK10FifteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join1At72 : joinSlice (tag 1) 72 24 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF17
