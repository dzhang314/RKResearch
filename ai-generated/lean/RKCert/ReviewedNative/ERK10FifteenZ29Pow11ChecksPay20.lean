module

public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenZ29Pow11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockPay20 : block payOK Count 20 24 = true := by decide +kernel

theorem blockPay21 : block payOK Count 21 24 = true := by decide +kernel

theorem blockPay22 : block payOK Count 22 24 = true := by decide +kernel

theorem blockPay23 : block payOK Count 23 24 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenZ29Pow11
