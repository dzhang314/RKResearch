module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData04
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData04Row034
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData04Row035
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData04Row036
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData04Row037
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData04Row038
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData04Row039
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData04Row040
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData04Row041

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows04 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows04 :=
  allWordRows_cons forces034 (allWordRows_cons forces035 (allWordRows_cons forces036 (allWordRows_cons forces037 (allWordRows_cons forces038 (allWordRows_cons forces039 (allWordRows_cons forces040 (allWordRows_cons forces041 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
