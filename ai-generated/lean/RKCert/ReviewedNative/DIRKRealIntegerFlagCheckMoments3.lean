module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_Q3 : checkScalar packet 3 = true := by decide +kernel
theorem chk_Q4 : checkScalar packet 4 = true := by decide +kernel
theorem chk_Q5 : checkScalar packet 5 = true := by decide +kernel
theorem chk_P3 : checkPrimitive packet 3 = true := by decide +kernel
theorem chk_P4 : checkPrimitive packet 4 = true := by decide +kernel
theorem chk_P5 : checkPrimitive packet 5 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
