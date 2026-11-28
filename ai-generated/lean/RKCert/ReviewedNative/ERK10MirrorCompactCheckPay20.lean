module

public import RKCert.ReviewedNative.ERK10MirrorCompactCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorCompact

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkPay20 : checkBlock payOK Count 20 16 = true := by decide +kernel
theorem checkPay21 : checkBlock payOK Count 21 16 = true := by decide +kernel
theorem checkPay22 : checkBlock payOK Count 22 16 = true := by decide +kernel
theorem checkPay23 : checkBlock payOK Count 23 16 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorCompact
