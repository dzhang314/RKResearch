module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks


@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks

open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_A8i2 : checkA packet 8 ⟨2, by decide +kernel⟩ = true := by decide +kernel
theorem chk_A8i3 : checkA packet 8 ⟨3, by decide +kernel⟩ = true := by decide +kernel

end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
