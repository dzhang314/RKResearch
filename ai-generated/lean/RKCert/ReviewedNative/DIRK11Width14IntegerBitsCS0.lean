module

public import RKCert.ReviewedNative.DIRK11Width14IntegerBlocks

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_c0 : blockC 0 = true := by decide +kernel
theorem chk_c1 : blockC 1 = true := by decide +kernel
theorem chk_c2 : blockC 2 = true := by decide +kernel
theorem chk_s0 : blockS 0 = true := by decide +kernel
theorem chk_s1 : blockS 1 = true := by decide +kernel
theorem chk_s2 : blockS 2 = true := by decide +kernel
end RKResearch.Certified.DIRK11Width14IntegerChecks
