module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_m6_0 : blockP 6 0 = true := by decide +kernel
theorem chk_m6_1 : blockP 6 1 = true := by decide +kernel
theorem chk_m6_2 : blockP 6 2 = true := by decide +kernel
theorem chk_m6_3 : blockP 6 3 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
