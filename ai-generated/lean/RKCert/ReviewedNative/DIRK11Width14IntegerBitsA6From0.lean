module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_a6_0 : blockARow 6 0 = true := by decide +kernel
theorem chk_a6_1 : blockARow 6 1 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
