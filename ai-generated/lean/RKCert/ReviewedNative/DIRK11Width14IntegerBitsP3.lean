module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_p3_3 : blockP 3 3 = true := by decide +kernel
theorem chk_p3_4 : blockP 3 4 = true := by decide +kernel
theorem chk_p3_5 : blockP 3 5 = true := by decide +kernel
theorem chk_p3_6 : blockP 3 6 = true := by decide +kernel
theorem chk_p3_7 : blockP 3 7 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
