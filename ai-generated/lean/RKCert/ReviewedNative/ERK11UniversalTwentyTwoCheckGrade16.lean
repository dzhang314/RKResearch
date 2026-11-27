module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkGrade16 : checkBlock gradeOK Count 16 64 = true := by decide +kernel
theorem checkGrade17 : checkBlock gradeOK Count 17 64 = true := by decide +kernel
theorem checkGrade18 : checkBlock gradeOK Count 18 64 = true := by decide +kernel
theorem checkGrade19 : checkBlock gradeOK Count 19 64 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
