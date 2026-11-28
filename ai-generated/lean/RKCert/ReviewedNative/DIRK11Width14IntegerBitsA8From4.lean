module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_a8_4 : blockARow 8 4 = true := by decide +kernel
theorem chk_a8_5 : blockARow 8 5 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
