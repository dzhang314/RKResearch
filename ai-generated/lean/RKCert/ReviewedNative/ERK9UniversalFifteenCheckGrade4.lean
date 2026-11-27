module

public import RKCert.ReviewedNative.ERK9UniversalFifteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9UniversalFifteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkGrade4 : checkBlock gradeOK Count 4 64 = true := by decide +kernel

end RKResearch.Certified.ERK9UniversalFifteen
