module

public import RKCert.ReviewedNative.ERK10MirrorCompactCore

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorCompact

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem checkGrade4 : checkBlock gradeOK Count 4 64 = true := by decide +kernel
theorem checkGrade5 : checkBlock gradeOK Count 5 64 = true := by decide +kernel
theorem checkGrade6 : checkBlock gradeOK Count 6 64 = true := by decide +kernel
theorem checkGrade7 : checkBlock gradeOK Count 7 64 = true := by decide +kernel

end RKResearch.Certified.ERK10MirrorCompact
