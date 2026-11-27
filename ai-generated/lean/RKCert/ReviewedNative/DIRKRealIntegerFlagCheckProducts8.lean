module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_m8_0 : blockP 8 0 = true := by decide +kernel
theorem chk_m8_1 : blockP 8 1 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
