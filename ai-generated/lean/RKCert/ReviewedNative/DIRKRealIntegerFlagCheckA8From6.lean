module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks


@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks

open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_A8i6 : checkA packet 8 ⟨6, by decide +kernel⟩ = true := by decide +kernel
theorem chk_A8i7 : checkA packet 8 ⟨7, by decide +kernel⟩ = true := by decide +kernel

end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
