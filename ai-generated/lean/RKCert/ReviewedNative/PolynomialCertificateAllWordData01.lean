module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData01
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData01Row008
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData01Row009
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData01Row010
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData01Row011
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData01Row013
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData01Row014
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData01Row015
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData01Row017

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem fullWordRows01 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows01 :=
  allWordRows_cons forces008 (allWordRows_cons forces009 (allWordRows_cons forces010 (allWordRows_cons forces011 (allWordRows_cons forces013 (allWordRows_cons forces014 (allWordRows_cons forces015 (allWordRows_cons forces017 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
