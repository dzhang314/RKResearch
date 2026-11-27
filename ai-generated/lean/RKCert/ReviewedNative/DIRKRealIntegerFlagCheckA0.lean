module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_A0 : blockA 0 = true := by decide +kernel
theorem chk_A1 : blockA 1 = true := by decide +kernel
theorem chk_A2 : blockA 2 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
