module

public import RKCert.ReviewedNative.ERK10SixteenF19Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF19

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockPay8 : block payOK Count 8 24 = true := by decide +kernel

theorem blockPay9 : block payOK Count 9 24 = true := by decide +kernel

theorem blockPay10 : block payOK Count 10 24 = true := by decide +kernel

theorem blockPay11 : block payOK Count 11 24 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF19
