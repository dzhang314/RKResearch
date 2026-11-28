module

public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenZ29Pow11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockGrade4 : block gradeOK Count 4 64 = true := by decide +kernel

theorem blockGrade5 : block gradeOK Count 5 64 = true := by decide +kernel

theorem blockGrade6 : block gradeOK Count 6 64 = true := by decide +kernel

theorem blockGrade7 : block gradeOK Count 7 64 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenZ29Pow11
