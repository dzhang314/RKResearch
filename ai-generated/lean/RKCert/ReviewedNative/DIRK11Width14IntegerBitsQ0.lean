module

public import RKCert.ReviewedNative.DIRK11Width14IntegerPowCache

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem chk_q0 : checkScalar packet 0 = true := by
  unfold checkScalar
  rw [pow_checked 0 (by decide)]
  decide +kernel
theorem chk_q1 : checkScalar packet 1 = true := by
  unfold checkScalar
  rw [pow_checked 1 (by decide)]
  decide +kernel
theorem chk_h0 : checkPrimitive packet 0 = true := by
  unfold checkPrimitive primitiveV
  rw [pow_checked 0 (by decide),pow_checked 1 (by decide)]
  decide +kernel
theorem chk_h1 : checkPrimitive packet 1 = true := by
  unfold checkPrimitive primitiveV
  rw [pow_checked 1 (by decide),pow_checked 2 (by decide)]
  decide +kernel

end RKResearch.Certified.DIRK11Width14IntegerChecks
