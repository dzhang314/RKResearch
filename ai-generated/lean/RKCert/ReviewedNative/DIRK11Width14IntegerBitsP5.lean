module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_p5_3 : blockP 5 3 = true := by decide +kernel
theorem chk_p5_4 : blockP 5 4 = true := by decide +kernel
theorem chk_p5_5 : blockP 5 5 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
