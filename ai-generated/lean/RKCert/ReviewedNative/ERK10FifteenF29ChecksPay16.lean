module

public import RKCert.ReviewedNative.ERK10FifteenF29Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockPay16 : block payOK Count 16 24 = true := by decide +kernel

theorem blockPay17 : block payOK Count 17 24 = true := by decide +kernel

theorem blockPay18 : block payOK Count 18 24 = true := by decide +kernel

theorem blockPay19 : block payOK Count 19 24 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF29
