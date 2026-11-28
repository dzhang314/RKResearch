module

public import RKCert.ReviewedNative.ERK10SixteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join0At168 : joinSlice (tag 0) 168 24 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF17
