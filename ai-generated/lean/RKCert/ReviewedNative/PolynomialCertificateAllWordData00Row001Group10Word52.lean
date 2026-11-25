module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData00

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

def groupPlan001_10_Word52 : GroupPortPlan :=
  [(markWords52, [⟨⟨[1, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 7], 0, 2, true⟩, true⟩, ⟨⟨[1, 4, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 4, 5, 7], 6, 2, false⟩, false⟩, ⟨⟨[1, 4, 5, 7, 3], 0, 1, false⟩, false⟩, ⟨⟨[1, 4, 5, 7, 2], 0, 1, false⟩, false⟩, ⟨⟨[1, 4, 5, 7, 3], 0, 1, true⟩, true⟩, ⟨⟨[1, 4, 5, 7, 2], 0, 1, true⟩, true⟩])]
theorem groupPlan001_10_Word52_ok : groupChecks row001 groupPlan001_10_Word52 = true := by decide +kernel

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
