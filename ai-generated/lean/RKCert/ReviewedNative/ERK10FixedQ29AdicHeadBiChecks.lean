module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadBi

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical.HeadBi

set_option maxRecDepth 50000
set_option maxHeartbeats 0

theorem cert_ratioD : guardedZero ratioD=true := by decide +kernel
theorem cert_ratioE : guardedZero ratioE=true := by decide +kernel
theorem cert_ratioB : guardedZero ratioB=true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Physical.HeadBi

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.HeadBi.cert_ratioB
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.HeadBi.cert_ratioD
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.HeadBi.cert_ratioE
