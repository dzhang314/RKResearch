module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_S6 : blockS 6 = true := by decide +kernel
theorem chk_S7 : blockS 7 = true := by decide +kernel
theorem chk_S8 : blockS 8 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
