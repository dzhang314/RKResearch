module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData03
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData03Row026
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData03Row027
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData03Row028
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData03Row029
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData03Row030
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData03Row031
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData03Row032
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData03Row033

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows03 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows03 :=
  allWordRows_cons forces026 (allWordRows_cons forces027 (allWordRows_cons forces028 (allWordRows_cons forces029 (allWordRows_cons forces030 (allWordRows_cons forces031 (allWordRows_cons forces032 (allWordRows_cons forces033 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
