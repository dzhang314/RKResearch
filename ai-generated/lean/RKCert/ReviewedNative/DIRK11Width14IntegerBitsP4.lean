module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_p4_3 : blockP 4 3 = true := by decide +kernel
theorem chk_p4_4 : blockP 4 4 = true := by decide +kernel
theorem chk_p4_5 : blockP 4 5 = true := by decide +kernel
theorem chk_p4_6 : blockP 4 6 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
