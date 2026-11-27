module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_m2_0 : blockP 2 0 = true := by decide +kernel
theorem chk_m2_1 : blockP 2 1 = true := by decide +kernel
theorem chk_m2_2 : blockP 2 2 = true := by decide +kernel
theorem chk_m2_3 : blockP 2 3 = true := by decide +kernel
theorem chk_m2_4 : blockP 2 4 = true := by decide +kernel
theorem chk_m2_5 : blockP 2 5 = true := by decide +kernel
theorem chk_m2_6 : blockP 2 6 = true := by decide +kernel
theorem chk_m2_7 : blockP 2 7 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
