module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_m7_0 : blockP 7 0 = true := by decide +kernel
theorem chk_m7_1 : blockP 7 1 = true := by decide +kernel
theorem chk_m7_2 : blockP 7 2 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
