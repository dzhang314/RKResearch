module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData10
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData10Row084
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData10Row085
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData10Row086
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData10Row087
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData10Row088
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData10Row089
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData10Row090
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData10Row091

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows10 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows10 :=
  allWordRows_cons forces084 (allWordRows_cons forces085 (allWordRows_cons forces086 (allWordRows_cons forces087 (allWordRows_cons forces088 (allWordRows_cons forces089 (allWordRows_cons forces090 (allWordRows_cons forces091 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
