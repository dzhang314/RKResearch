module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_c9 : blockC 9 = true := by decide +kernel
theorem chk_s9 : blockS 9 = true := by decide +kernel
theorem chk_s10 : blockS 10 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
