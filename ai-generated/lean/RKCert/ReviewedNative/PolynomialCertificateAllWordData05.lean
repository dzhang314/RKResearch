module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData05
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData05Row043
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData05Row045
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData05Row046
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData05Row047
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData05Row048
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData05Row049
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData05Row050L
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData05Row050R
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData05Row051

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem forces050 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordCage K allMarkGroups row050 := by
  apply allWordCage_join (slot := 1) (cut := 4032)
  · rw [← sub050L_eq]
    exact @forces050L K _ _ _
  · rw [← sub050R_eq]
    exact @forces050R K _ _ _

theorem fullWordRows05 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows05 :=
  allWordRows_cons forces043 (allWordRows_cons forces045 (allWordRows_cons forces046 (allWordRows_cons forces047 (allWordRows_cons forces048 (allWordRows_cons forces049 (allWordRows_cons forces050 (allWordRows_cons forces051 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
