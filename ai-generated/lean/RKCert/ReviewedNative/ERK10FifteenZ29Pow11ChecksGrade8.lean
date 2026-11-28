module

public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Core

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenZ29Pow11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockGrade8 : block gradeOK Count 8 64 = true := by decide +kernel

theorem blockGrade9 : block gradeOK Count 9 64 = true := by decide +kernel

theorem blockGrade10 : block gradeOK Count 10 64 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenZ29Pow11
