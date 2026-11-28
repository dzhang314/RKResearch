module

public import RKCert.ReviewedNative.ERK10SixteenF13Join5At0
public import RKCert.ReviewedNative.ERK10SixteenF13Join5At24

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF13

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join5 : joinOK (tag 5) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 5)) = 25)
  have H0 := join5At0
  have H1 := glueJoin H0 join5At24
  exact H1


end RKResearch.Certified.ERK10SixteenF13
