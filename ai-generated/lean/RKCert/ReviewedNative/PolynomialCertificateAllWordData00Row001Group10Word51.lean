module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData00

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

def groupPlan001_10_Word51 : GroupPortPlan :=
  [(markWords51, [⟨⟨[1, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 6], 0, 2, true⟩, true⟩, ⟨⟨[1, 4, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 4, 5, 6], 7, 2, false⟩, true⟩, ⟨⟨[1, 4, 5, 6, 2], 7, 1, true⟩, false⟩, ⟨⟨[1, 4, 5, 6, 3], 7, 1, true⟩, false⟩, ⟨⟨[1, 4, 5, 6, 2], 7, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 6, 3], 7, 1, false⟩, true⟩])]
theorem groupPlan001_10_Word51_ok : groupChecks row001 groupPlan001_10_Word51 = true := by decide +kernel

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
