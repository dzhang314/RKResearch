module

public import RKCert.ReviewedNative.ERK10FifteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join0At312 : joinSlice (tag 0) 312 12 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF17
