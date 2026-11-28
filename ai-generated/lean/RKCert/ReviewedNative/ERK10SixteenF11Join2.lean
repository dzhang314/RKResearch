module

public import RKCert.ReviewedNative.ERK10SixteenF11Join2At0
public import RKCert.ReviewedNative.ERK10SixteenF11Join2At24
public import RKCert.ReviewedNative.ERK10SixteenF11Join2At48

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join2 : joinOK (tag 2) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 2)) = 50)
  have H0 := join2At0
  have H1 := glueJoin H0 join2At24
  have H2 := glueJoin H1 join2At48
  exact H2


end RKResearch.Certified.ERK10SixteenF11
