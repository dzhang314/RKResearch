module

public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join7At0
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join7At24

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenZ29Pow11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join7 : joinOK (tag 7) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 7)) = 32)
  have H0 := join7At0
  have H1 := glueJoin H0 join7At24
  exact H1


end RKResearch.Certified.ERK10FifteenZ29Pow11
