module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData13
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData13Row108
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData13Row109
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData13Row110
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData13Row111
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData13Row112
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData13Row113
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData13Row114
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData13Row115

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows13 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows13 :=
  allWordRows_cons forces108 (allWordRows_cons forces109 (allWordRows_cons forces110 (allWordRows_cons forces111 (allWordRows_cons forces112 (allWordRows_cons forces113 (allWordRows_cons forces114 (allWordRows_cons forces115 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
