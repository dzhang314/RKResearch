module

public import RKCert.ReviewedNative.ERK10UniversalNineteenCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalNineteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkGrade8 : checkBlock gradeOK Count 8 64 = true := by decide +kernel
theorem checkGrade9 : checkBlock gradeOK Count 9 64 = true := by decide +kernel

end RKResearch.Certified.ERK10UniversalNineteen
