module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData08
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData08Row068
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData08Row069
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData08Row070
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData08Row071
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData08Row072
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData08Row073
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData08Row074
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData08Row075

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows08 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows08 :=
  allWordRows_cons forces068 (allWordRows_cons forces069 (allWordRows_cons forces070 (allWordRows_cons forces071 (allWordRows_cons forces072 (allWordRows_cons forces073 (allWordRows_cons forces074 (allWordRows_cons forces075 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
