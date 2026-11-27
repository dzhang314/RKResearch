module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkGrade12 : checkBlock gradeOK Count 12 64 = true := by decide +kernel
theorem checkGrade13 : checkBlock gradeOK Count 13 64 = true := by decide +kernel
theorem checkGrade14 : checkBlock gradeOK Count 14 64 = true := by decide +kernel
theorem checkGrade15 : checkBlock gradeOK Count 15 64 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
