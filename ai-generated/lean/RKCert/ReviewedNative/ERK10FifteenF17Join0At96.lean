module

public import RKCert.ReviewedNative.ERK10FifteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join0At96 : joinSlice (tag 0) 96 24 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF17
