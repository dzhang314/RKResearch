module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_Q6 : checkScalar packet 6 = true := by decide +kernel
theorem chk_Q7 : checkScalar packet 7 = true := by decide +kernel
theorem chk_Q8 : checkScalar packet 8 = true := by decide +kernel
theorem chk_P6 : checkPrimitive packet 6 = true := by decide +kernel
theorem chk_P7 : checkPrimitive packet 7 = true := by decide +kernel
theorem chk_P8 : checkPrimitive packet 8 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
