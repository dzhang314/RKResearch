module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData07
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData07Row060
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData07Row061
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData07Row062
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData07Row063
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData07Row064
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData07Row065
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData07Row066
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData07Row067

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows07 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows07 :=
  allWordRows_cons forces060 (allWordRows_cons forces061 (allWordRows_cons forces062 (allWordRows_cons forces063 (allWordRows_cons forces064 (allWordRows_cons forces065 (allWordRows_cons forces066 (allWordRows_cons forces067 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
