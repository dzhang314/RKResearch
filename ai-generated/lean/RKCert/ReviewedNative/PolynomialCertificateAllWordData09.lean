module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData09
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData09Row076
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData09Row077
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData09Row078
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData09Row079
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData09Row080
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData09Row081
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData09Row082
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData09Row083

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows09 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows09 :=
  allWordRows_cons forces076 (allWordRows_cons forces077 (allWordRows_cons forces078 (allWordRows_cons forces079 (allWordRows_cons forces080 (allWordRows_cons forces081 (allWordRows_cons forces082 (allWordRows_cons forces083 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
