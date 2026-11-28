module

public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenZ29Pow11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockPay24 : block payOK Count 24 24 = true := by decide +kernel

theorem blockPay25 : block payOK Count 25 24 = true := by decide +kernel

theorem blockPay26 : block payOK Count 26 24 = true := by decide +kernel

theorem blockPay27 : block payOK Count 27 24 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenZ29Pow11
