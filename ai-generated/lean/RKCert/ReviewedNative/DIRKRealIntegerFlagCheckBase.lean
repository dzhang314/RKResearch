module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagCheckBlocks

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem chk_node : checkNode packet = true := by decide +kernel
theorem chk_bush : checkBush packet = true := by decide +kernel
end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
