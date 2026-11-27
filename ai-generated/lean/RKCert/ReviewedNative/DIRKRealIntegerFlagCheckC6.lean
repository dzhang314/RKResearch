module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_C6 : blockC 6 = true := by decide +kernel
theorem chk_C7 : blockC 7 = true := by decide +kernel
theorem chk_C8 : blockC 8 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
