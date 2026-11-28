module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_a9_2 : blockARow 9 2 = true := by decide +kernel
theorem chk_a9_3 : blockARow 9 3 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
