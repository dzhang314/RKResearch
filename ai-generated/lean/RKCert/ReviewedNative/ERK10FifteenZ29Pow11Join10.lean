module

public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join10At0

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenZ29Pow11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join10 : joinOK (tag 10) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 10)) = 16)
  have H0 := join10At0
  exact H0


end RKResearch.Certified.ERK10FifteenZ29Pow11
