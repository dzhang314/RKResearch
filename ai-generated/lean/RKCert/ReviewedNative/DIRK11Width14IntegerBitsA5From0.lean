module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_a5_0 : blockARow 5 0 = true := by decide +kernel
theorem chk_a5_1 : blockARow 5 1 = true := by decide +kernel
theorem chk_a5_2 : blockARow 5 2 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
