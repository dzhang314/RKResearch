module

public import RKCert.ReviewedNative.ERK10SixteenF19Join4At0
public import RKCert.ReviewedNative.ERK10SixteenF19Join4At24

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF19

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join4 : joinOK (tag 4) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 4)) = 25)
  have H0 := join4At0
  have H1 := glueJoin H0 join4At24
  exact H1


end RKResearch.Certified.ERK10SixteenF19
