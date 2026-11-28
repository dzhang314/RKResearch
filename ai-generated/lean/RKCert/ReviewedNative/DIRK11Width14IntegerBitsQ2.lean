module

public import RKCert.ReviewedNative.DIRK11Width14IntegerPowCache

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_q2 : checkScalar packet 2 = true := by
  unfold checkScalar
  rw [pow_checked 2 (by decide)]
  decide +kernel
theorem chk_q3 : checkScalar packet 3 = true := by
  unfold checkScalar
  rw [pow_checked 3 (by decide)]
  decide +kernel
theorem chk_h2 : checkPrimitive packet 2 = true := by
  unfold checkPrimitive primitiveV
  rw [pow_checked 2 (by decide),pow_checked 3 (by decide)]
  decide +kernel
theorem chk_h3 : checkPrimitive packet 3 = true := by
  unfold checkPrimitive primitiveV
  rw [pow_checked 3 (by decide),pow_checked 4 (by decide)]
  decide +kernel

end RKResearch.Certified.DIRK11Width14IntegerChecks
