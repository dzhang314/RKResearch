module

public import RKCert.ReviewedNative.ERK11UniversalTwentyTwoCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK11UniversalTwentyTwo

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkGrade20 : checkBlock gradeOK Count 20 64 = true := by decide +kernel
theorem checkGrade21 : checkBlock gradeOK Count 21 64 = true := by decide +kernel
theorem checkGrade22 : checkBlock gradeOK Count 22 64 = true := by decide +kernel
theorem checkGrade23 : checkBlock gradeOK Count 23 64 = true := by decide +kernel

end RKResearch.Certified.ERK11UniversalTwentyTwo
