module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_m5_0 : blockP 5 0 = true := by decide +kernel
theorem chk_m5_1 : blockP 5 1 = true := by decide +kernel
theorem chk_m5_2 : blockP 5 2 = true := by decide +kernel
theorem chk_m5_3 : blockP 5 3 = true := by decide +kernel
theorem chk_m5_4 : blockP 5 4 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
