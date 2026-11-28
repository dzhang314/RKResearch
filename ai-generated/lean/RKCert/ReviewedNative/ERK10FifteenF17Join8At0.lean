module

public import RKCert.ReviewedNative.ERK10FifteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join8At0 : joinSlice (tag 8) 0 16 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF17
