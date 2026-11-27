module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_C0 : blockC 0 = true := by decide +kernel
theorem chk_C1 : blockC 1 = true := by decide +kernel
theorem chk_C2 : blockC 2 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
