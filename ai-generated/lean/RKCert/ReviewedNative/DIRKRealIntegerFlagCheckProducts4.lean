module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_m4_0 : blockP 4 0 = true := by decide +kernel
theorem chk_m4_1 : blockP 4 1 = true := by decide +kernel
theorem chk_m4_2 : blockP 4 2 = true := by decide +kernel
theorem chk_m4_3 : blockP 4 3 = true := by decide +kernel
theorem chk_m4_4 : blockP 4 4 = true := by decide +kernel
theorem chk_m4_5 : blockP 4 5 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
