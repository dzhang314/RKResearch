module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_m1_0 : blockP 1 0 = true := by decide +kernel
theorem chk_m1_1 : blockP 1 1 = true := by decide +kernel
theorem chk_m1_2 : blockP 1 2 = true := by decide +kernel
theorem chk_m1_3 : blockP 1 3 = true := by decide +kernel
theorem chk_m1_4 : blockP 1 4 = true := by decide +kernel
theorem chk_m1_5 : blockP 1 5 = true := by decide +kernel
theorem chk_m1_6 : blockP 1 6 = true := by decide +kernel
theorem chk_m1_7 : blockP 1 7 = true := by decide +kernel
theorem chk_m1_8 : blockP 1 8 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
