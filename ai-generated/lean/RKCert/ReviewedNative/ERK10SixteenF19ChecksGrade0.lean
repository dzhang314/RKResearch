module

public import RKCert.ReviewedNative.ERK10SixteenF19Core

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF19

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockGrade0 : block gradeOK Count 0 64 = true := by decide +kernel

theorem blockGrade1 : block gradeOK Count 1 64 = true := by decide +kernel

theorem blockGrade2 : block gradeOK Count 2 64 = true := by decide +kernel

theorem blockGrade3 : block gradeOK Count 3 64 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF19
