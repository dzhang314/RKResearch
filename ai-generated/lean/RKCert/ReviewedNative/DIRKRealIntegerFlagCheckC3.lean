module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_C3 : blockC 3 = true := by decide +kernel
theorem chk_C4 : blockC 4 = true := by decide +kernel
theorem chk_C5 : blockC 5 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
