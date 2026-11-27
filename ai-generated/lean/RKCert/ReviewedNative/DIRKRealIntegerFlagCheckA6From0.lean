module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks


@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks

open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_A6i0 : checkA packet 6 ⟨0, by decide +kernel⟩ = true := by decide +kernel
theorem chk_A6i1 : checkA packet 6 ⟨1, by decide +kernel⟩ = true := by decide +kernel

end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
