module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_S0 : blockS 0 = true := by decide +kernel
theorem chk_S1 : blockS 1 = true := by decide +kernel
theorem chk_S2 : blockS 2 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
