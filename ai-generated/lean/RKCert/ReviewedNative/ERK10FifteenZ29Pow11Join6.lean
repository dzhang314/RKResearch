module

public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join6At0
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join6At24

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenZ29Pow11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join6 : joinOK (tag 6) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 6)) = 32)
  have H0 := join6At0
  have H1 := glueJoin H0 join6At24
  exact H1


end RKResearch.Certified.ERK10FifteenZ29Pow11
