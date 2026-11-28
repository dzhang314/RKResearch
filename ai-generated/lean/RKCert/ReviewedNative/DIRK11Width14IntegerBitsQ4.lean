module

public import RKCert.ReviewedNative.DIRK11Width14IntegerPowCache

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_q4 : checkScalar packet 4 = true := by
  unfold checkScalar
  rw [pow_checked 4 (by decide)]
  decide +kernel
theorem chk_q5 : checkScalar packet 5 = true := by
  unfold checkScalar
  rw [pow_checked 5 (by decide)]
  decide +kernel
theorem chk_h4 : checkPrimitive packet 4 = true := by
  unfold checkPrimitive primitiveV
  rw [pow_checked 4 (by decide),pow_checked 5 (by decide)]
  decide +kernel
theorem chk_h5 : checkPrimitive packet 5 = true := by
  unfold checkPrimitive primitiveV
  rw [pow_checked 5 (by decide),pow_checked 6 (by decide)]
  decide +kernel

end RKResearch.Certified.DIRK11Width14IntegerChecks
