module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData00

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

def groupPlan001_09_Word49 : GroupPortPlan :=
  [(markWords49, [⟨⟨[1, 3, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 7], 0, 2, true⟩, true⟩, ⟨⟨[1, 3, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 3, 5, 7], 6, 2, false⟩, false⟩, ⟨⟨[1, 3, 5, 7, 4], 0, 1, false⟩, false⟩, ⟨⟨[1, 3, 5, 7, 2], 0, 1, false⟩, false⟩, ⟨⟨[1, 3, 5, 7, 4], 0, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 7, 2], 0, 1, true⟩, true⟩])]
theorem groupPlan001_09_Word49_ok : groupChecks row001 groupPlan001_09_Word49 = true := by decide +kernel

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
