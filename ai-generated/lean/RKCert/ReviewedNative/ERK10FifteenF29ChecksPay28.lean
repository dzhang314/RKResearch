module

public import RKCert.ReviewedNative.ERK10FifteenF29Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockPay28 : block payOK Count 28 24 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF29
