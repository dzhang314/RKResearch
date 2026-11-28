module

public import RKCert.ReviewedNative.ERK10SixteenF23Join12At0

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF23

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join12 : joinOK (tag 12) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 12)) = 13)
  have H0 := join12At0
  exact H0


end RKResearch.Certified.ERK10SixteenF23
