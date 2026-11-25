module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData00

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

def groupPlan001_10_Word53to54 : GroupPortPlan :=
  [(markWords53, [⟨⟨[1, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 6, 7], 0, 1, true⟩, true⟩, ⟨⟨[1, 4, 6, 7], 5, 1, true⟩, true⟩, ⟨⟨[1, 4, 6, 7], 3, 1, true⟩, true⟩, ⟨⟨[1, 4, 6, 7], 2, 1, true⟩, true⟩]),
   (markWords54, [⟨⟨[1, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 5, 6, 7], 4, 2, false⟩, false⟩, ⟨⟨[1, 5, 6, 7], 3, 2, false⟩, false⟩, ⟨⟨[1, 5, 6, 7], 2, 2, false⟩, false⟩])]
theorem groupPlan001_10_Word53to54_ok : groupChecks row001 groupPlan001_10_Word53to54 = true := by decide +kernel

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
