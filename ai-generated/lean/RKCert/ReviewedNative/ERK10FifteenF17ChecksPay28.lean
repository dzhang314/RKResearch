module

public import RKCert.ReviewedNative.ERK10FifteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockPay28 : block payOK Count 28 24 = true := by decide +kernel

theorem blockPay29 : block payOK Count 29 24 = true := by decide +kernel

theorem blockPay30 : block payOK Count 30 24 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF17
