module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_m3_0 : blockP 3 0 = true := by decide +kernel
theorem chk_m3_1 : blockP 3 1 = true := by decide +kernel
theorem chk_m3_2 : blockP 3 2 = true := by decide +kernel
theorem chk_m3_3 : blockP 3 3 = true := by decide +kernel
theorem chk_m3_4 : blockP 3 4 = true := by decide +kernel
theorem chk_m3_5 : blockP 3 5 = true := by decide +kernel
theorem chk_m3_6 : blockP 3 6 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
