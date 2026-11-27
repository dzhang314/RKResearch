module

public import RKCert.ReviewedNative.DIRK10RationalTwelveAlternateFlagReplayData

@[expose] public section

namespace RKResearch.Certified.DIRK10RationalTwelveAlternateFlagReplay
open RKResearch RationalFlagReplay
open scoped Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem node : checkNode packet = true := by decide +kernel
theorem primitive0 : checkPrimitive packet 0 = true := by decide +kernel
theorem primitive1 : checkPrimitive packet 1 = true := by decide +kernel
theorem primitive2 : checkPrimitive packet 2 = true := by decide +kernel
theorem primitive3 : checkPrimitive packet 3 = true := by decide +kernel
theorem primitive4 : checkPrimitive packet 4 = true := by decide +kernel
theorem primitive5 : checkPrimitive packet 5 = true := by decide +kernel
theorem primitive6 : checkPrimitive packet 6 = true := by decide +kernel
theorem primitive7 : checkPrimitive packet 7 = true := by decide +kernel
theorem primitive8 : checkPrimitive packet 8 = true := by decide +kernel
theorem scalar0 : checkScalar packet 0 = true := by decide +kernel
theorem scalar1 : checkScalar packet 1 = true := by decide +kernel
theorem scalar2 : checkScalar packet 2 = true := by decide +kernel
theorem scalar3 : checkScalar packet 3 = true := by decide +kernel
theorem scalar4 : checkScalar packet 4 = true := by decide +kernel
theorem scalar5 : checkScalar packet 5 = true := by decide +kernel
theorem scalar6 : checkScalar packet 6 = true := by decide +kernel
theorem scalar7 : checkScalar packet 7 = true := by decide +kernel
theorem scalar8 : checkScalar packet 8 = true := by decide +kernel
theorem scalar9 : checkScalar packet 9 = true := by decide +kernel
theorem next_star : bushResidual packet 10 = (19891 : ℚ)/520224768 := by decide +kernel

end RKResearch.Certified.DIRK10RationalTwelveAlternateFlagReplay
