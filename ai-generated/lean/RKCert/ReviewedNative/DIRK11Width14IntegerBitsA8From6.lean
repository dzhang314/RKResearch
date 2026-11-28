module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_a8_6 : blockARow 8 6 = true := by decide +kernel
theorem chk_a8_7 : blockARow 8 7 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
