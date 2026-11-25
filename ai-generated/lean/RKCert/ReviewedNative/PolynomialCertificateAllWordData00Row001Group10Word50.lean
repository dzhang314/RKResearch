module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData00

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

def groupPlan001_10_Word50 : GroupPortPlan :=
  [(markWords50, [⟨⟨[1, 3, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 6, 7], 0, 1, true⟩, true⟩, ⟨⟨[1, 3, 6, 7], 5, 1, true⟩, true⟩, ⟨⟨[1, 3, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[1, 3, 6, 7], 2, 1, true⟩, true⟩])]
theorem groupPlan001_10_Word50_ok : groupChecks row001 groupPlan001_10_Word50 = true := by decide +kernel

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
