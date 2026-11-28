module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_c6 : blockC 6 = true := by decide +kernel
theorem chk_c7 : blockC 7 = true := by decide +kernel
theorem chk_c8 : blockC 8 = true := by decide +kernel
theorem chk_s6 : blockS 6 = true := by decide +kernel
theorem chk_s7 : blockS 7 = true := by decide +kernel
theorem chk_s8 : blockS 8 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
