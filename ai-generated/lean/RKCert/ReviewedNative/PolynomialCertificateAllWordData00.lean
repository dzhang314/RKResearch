module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData00
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row000
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row001
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row002
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row003
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row004
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row005
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row006
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row007

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows00 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows00 :=
  allWordRows_cons forces000 (allWordRows_cons forces001 (allWordRows_cons forces002 (allWordRows_cons forces003 (allWordRows_cons forces004 (allWordRows_cons forces005 (allWordRows_cons forces006 (allWordRows_cons forces007 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
