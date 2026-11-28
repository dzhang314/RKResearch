module

public import RKCert.ReviewedNative.ERK10FifteenF29Join15At0

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenF29

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem join15 : joinOK (tag 15) = true := by
  apply finishJoin (by decide +kernel : cut (10-grade (tag 15)) = 16)
  have H0 := join15At0
  exact H0


end RKResearch.Certified.ERK10FifteenF29
