module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_a9_0 : blockARow 9 0 = true := by decide +kernel
theorem chk_a9_1 : blockARow 9 1 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
