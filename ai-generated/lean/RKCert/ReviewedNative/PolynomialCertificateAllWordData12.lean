module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData12
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData12Row100
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData12Row101
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData12Row102
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData12Row103
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData12Row104
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData12Row105
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData12Row106
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData12Row107

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows12 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows12 :=
  allWordRows_cons forces100 (allWordRows_cons forces101 (allWordRows_cons forces102 (allWordRows_cons forces103 (allWordRows_cons forces104 (allWordRows_cons forces105 (allWordRows_cons forces106 (allWordRows_cons forces107 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
