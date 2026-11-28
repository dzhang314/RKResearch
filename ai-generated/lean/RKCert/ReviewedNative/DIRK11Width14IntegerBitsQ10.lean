module

public import RKCert.ReviewedNative.DIRK11Width14IntegerPowCache

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_q10 : checkScalar packet 10 = true := by
  unfold checkScalar
  rw [pow_checked 10 (by decide)]
  decide +kernel

end RKResearch.Certified.DIRK11Width14IntegerChecks
