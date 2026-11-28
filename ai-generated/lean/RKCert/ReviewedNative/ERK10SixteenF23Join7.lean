module

public import RKCert.ReviewedNative.ERK10SixteenF23Join7At0

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF23

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join7 : joinOK (tag 7) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 7)) = 13)
  have H0 := join7At0
  exact H0


end RKResearch.Certified.ERK10SixteenF23
