module

public import RKCert.ReviewedNative.ERK10FifteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join2At48 : joinSlice (tag 2) 48 19 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF17
