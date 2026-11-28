module

public import RKCert.ReviewedNative.ERK10SixteenF17Join10At0

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join10 : joinOK (tag 10) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 10)) = 13)
  have H0 := join10At0
  exact H0


end RKResearch.Certified.ERK10SixteenF17
