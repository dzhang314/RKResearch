module

public import RKCert.ReviewedNative.ERK10UniversalEighteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalEighteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkGrade8 : checkBlock gradeOK Count 8 64 = true := by decide +kernel
theorem checkGrade9 : checkBlock gradeOK Count 9 64 = true := by decide +kernel
theorem checkGrade10 : checkBlock gradeOK Count 10 64 = true := by decide +kernel
theorem checkGrade11 : checkBlock gradeOK Count 11 64 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalEighteen
