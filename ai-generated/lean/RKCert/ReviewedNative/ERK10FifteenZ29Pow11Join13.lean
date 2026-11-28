module

public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join13At0

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenZ29Pow11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join13 : joinOK (tag 13) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 13)) = 16)
  have H0 := join13At0
  exact H0


end RKResearch.Certified.ERK10FifteenZ29Pow11
