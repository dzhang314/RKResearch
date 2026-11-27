module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_A3 : blockA 3 = true := by decide +kernel
theorem chk_A4 : blockA 4 = true := by decide +kernel
theorem chk_A5 : blockA 5 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
