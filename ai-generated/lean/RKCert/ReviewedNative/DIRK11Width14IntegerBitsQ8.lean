module

public import RKCert.ReviewedNative.DIRK11Width14IntegerPowCache

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_q8 : checkScalar packet 8 = true := by
  unfold checkScalar
  rw [pow_checked 8 (by decide)]
  decide +kernel
theorem chk_q9 : checkScalar packet 9 = true := by
  unfold checkScalar
  rw [pow_checked 9 (by decide)]
  decide +kernel
theorem chk_h8 : checkPrimitive packet 8 = true := by
  unfold checkPrimitive primitiveV
  rw [pow_checked 8 (by decide),pow_checked 9 (by decide)]
  decide +kernel
theorem chk_h9 : checkPrimitive packet 9 = true := by
  unfold checkPrimitive primitiveV
  rw [pow_checked 9 (by decide),pow_checked 10 (by decide)]
  decide +kernel

end RKResearch.Certified.DIRK11Width14IntegerChecks
