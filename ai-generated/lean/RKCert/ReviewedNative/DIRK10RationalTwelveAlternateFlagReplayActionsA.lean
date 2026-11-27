module

public import RKCert.ReviewedNative.DIRK10RationalTwelveAlternateFlagReplayData

@[expose] public section

namespace RKResearch.Certified.DIRK10RationalTwelveAlternateFlagReplay
open RKResearch RationalFlagReplay
open scoped Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem actA0 : blockA 0 = true := by decide +kernel
theorem actA1 : blockA 1 = true := by decide +kernel
theorem actA2 : blockA 2 = true := by decide +kernel
theorem actA3 : blockA 3 = true := by decide +kernel
theorem actA4 : blockA 4 = true := by decide +kernel
theorem actA5 : blockA 5 = true := by decide +kernel
theorem actA6 : blockA 6 = true := by decide +kernel
theorem actA7 : blockA 7 = true := by decide +kernel
theorem actA8 : blockA 8 = true := by decide +kernel

end RKResearch.Certified.DIRK10RationalTwelveAlternateFlagReplay
