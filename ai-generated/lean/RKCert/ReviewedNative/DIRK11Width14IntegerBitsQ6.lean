module

public import RKCert.ReviewedNative.DIRK11Width14IntegerPowCache

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_q6 : checkScalar packet 6 = true := by
  unfold checkScalar
  rw [pow_checked 6 (by decide)]
  decide +kernel
theorem chk_q7 : checkScalar packet 7 = true := by
  unfold checkScalar
  rw [pow_checked 7 (by decide)]
  decide +kernel
theorem chk_h6 : checkPrimitive packet 6 = true := by
  unfold checkPrimitive primitiveV
  rw [pow_checked 6 (by decide),pow_checked 7 (by decide)]
  decide +kernel
theorem chk_h7 : checkPrimitive packet 7 = true := by
  unfold checkPrimitive primitiveV
  rw [pow_checked 7 (by decide),pow_checked 8 (by decide)]
  decide +kernel

end RKResearch.Certified.DIRK11Width14IntegerChecks
