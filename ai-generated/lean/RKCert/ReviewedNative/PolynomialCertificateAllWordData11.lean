module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData11
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData11Row092
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData11Row093
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData11Row094
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData11Row095
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData11Row096
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData11Row097
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData11Row098
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData11Row099

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows11 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows11 :=
  allWordRows_cons forces092 (allWordRows_cons forces093 (allWordRows_cons forces094 (allWordRows_cons forces095 (allWordRows_cons forces096 (allWordRows_cons forces097 (allWordRows_cons forces098 (allWordRows_cons forces099 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
