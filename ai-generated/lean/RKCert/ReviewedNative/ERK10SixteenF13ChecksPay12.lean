module

public import RKCert.ReviewedNative.ERK10SixteenF13Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF13

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockPay12 : block payOK Count 12 24 = true := by decide +kernel

theorem blockPay13 : block payOK Count 13 24 = true := by decide +kernel

theorem blockPay14 : block payOK Count 14 24 = true := by decide +kernel

theorem blockPay15 : block payOK Count 15 24 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF13
