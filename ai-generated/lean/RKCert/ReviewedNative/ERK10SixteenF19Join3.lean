module

public import RKCert.ReviewedNative.ERK10SixteenF19Join3At0
public import RKCert.ReviewedNative.ERK10SixteenF19Join3At24
public import RKCert.ReviewedNative.ERK10SixteenF19Join3At48

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF19

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join3 : joinOK (tag 3) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 3)) = 50)
  have H0 := join3At0
  have H1 := glueJoin H0 join3At24
  have H2 := glueJoin H1 join3At48
  exact H2


end RKResearch.Certified.ERK10SixteenF19
