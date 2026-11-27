module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_S3 : blockS 3 = true := by decide +kernel
theorem chk_S4 : blockS 4 = true := by decide +kernel
theorem chk_S5 : blockS 5 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
