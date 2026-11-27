module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_Q0 : checkScalar packet 0 = true := by decide +kernel
theorem chk_Q1 : checkScalar packet 1 = true := by decide +kernel
theorem chk_Q2 : checkScalar packet 2 = true := by decide +kernel
theorem chk_P0 : checkPrimitive packet 0 = true := by decide +kernel
theorem chk_P1 : checkPrimitive packet 1 = true := by decide +kernel
theorem chk_P2 : checkPrimitive packet 2 = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
