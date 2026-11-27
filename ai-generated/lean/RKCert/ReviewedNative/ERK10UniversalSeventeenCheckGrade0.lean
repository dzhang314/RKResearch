module

public import RKCert.ReviewedNative.ERK10UniversalSeventeenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalSeventeen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkGrade0 : checkBlock gradeOK Count 0 64 = true := by decide +kernel
theorem checkGrade1 : checkBlock gradeOK Count 1 64 = true := by decide +kernel
theorem checkGrade2 : checkBlock gradeOK Count 2 64 = true := by decide +kernel
theorem checkGrade3 : checkBlock gradeOK Count 3 64 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalSeventeen
