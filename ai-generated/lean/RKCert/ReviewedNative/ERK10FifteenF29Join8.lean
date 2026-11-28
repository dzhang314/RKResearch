module

public import RKCert.ReviewedNative.ERK10FifteenF29Join8At0

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join8 : joinOK (tag 8) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 8)) = 16)
  have H0 := join8At0
  exact H0


end RKResearch.Certified.ERK10FifteenF29
