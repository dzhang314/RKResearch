module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkGrade24 : checkBlock gradeOK Count 24 64 = true := by decide +kernel
theorem checkGrade25 : checkBlock gradeOK Count 25 64 = true := by decide +kernel
theorem checkGrade26 : checkBlock gradeOK Count 26 64 = true := by decide +kernel
theorem checkGrade27 : checkBlock gradeOK Count 27 64 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
