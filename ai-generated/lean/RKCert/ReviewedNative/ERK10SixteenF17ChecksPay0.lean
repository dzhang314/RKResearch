module

public import RKCert.ReviewedNative.ERK10SixteenF17Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockPay0 : block payOK Count 0 24 = true := by decide +kernel

theorem blockPay1 : block payOK Count 1 24 = true := by decide +kernel

theorem blockPay2 : block payOK Count 2 24 = true := by decide +kernel

theorem blockPay3 : block payOK Count 3 24 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF17
