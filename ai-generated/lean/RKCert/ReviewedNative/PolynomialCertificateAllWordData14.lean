module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData14
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData14Row116
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData14Row117
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData14Row118
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData14Row119
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData14Row120
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData14Row121
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData14Row122
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData14Row123

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows14 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows14 :=
  allWordRows_cons forces116 (allWordRows_cons forces117 (allWordRows_cons forces118 (allWordRows_cons forces119 (allWordRows_cons forces120 (allWordRows_cons forces121 (allWordRows_cons forces122 (allWordRows_cons forces123 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
