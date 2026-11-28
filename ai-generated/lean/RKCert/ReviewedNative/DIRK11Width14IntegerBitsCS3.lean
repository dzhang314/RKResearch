module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_c3 : blockC 3 = true := by decide +kernel
theorem chk_c4 : blockC 4 = true := by decide +kernel
theorem chk_c5 : blockC 5 = true := by decide +kernel
theorem chk_s3 : blockS 3 = true := by decide +kernel
theorem chk_s4 : blockS 4 = true := by decide +kernel
theorem chk_s5 : blockS 5 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
