module

public import RKCert.ReviewedNative.ERK10FifteenF29Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockPay4 : block payOK Count 4 24 = true := by decide +kernel

theorem blockPay5 : block payOK Count 5 24 = true := by decide +kernel

theorem blockPay6 : block payOK Count 6 24 = true := by decide +kernel

theorem blockPay7 : block payOK Count 7 24 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenF29
