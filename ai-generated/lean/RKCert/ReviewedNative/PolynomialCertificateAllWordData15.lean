module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData15
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData15Row124
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData15Row125
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData15Row126

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows15 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows15 :=
  allWordRows_cons forces124 (allWordRows_cons forces125 (allWordRows_cons forces126 (allWordRows_nil)))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
