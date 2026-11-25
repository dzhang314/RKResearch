module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData06
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData06Row052
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData06Row053
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData06Row054L
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData06Row054R
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData06Row055
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData06Row056
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData06Row057
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData06Row058L
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData06Row058R
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData06Row059

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem forces054 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordCage K allMarkGroups row054 := by
  apply allWordCage_join (slot := 2) (cut := 3810)
  · rw [← sub054L_eq]
    exact @forces054L K _ _ _
  · rw [← sub054R_eq]
    exact @forces054R K _ _ _

theorem forces058 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordCage K allMarkGroups row058 := by
  apply allWordCage_join (slot := 4) (cut := 16845)
  · rw [← sub058L_eq]
    exact @forces058L K _ _ _
  · rw [← sub058R_eq]
    exact @forces058R K _ _ _

theorem fullWordRows06 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows06 :=
  allWordRows_cons forces052 (allWordRows_cons forces053 (allWordRows_cons forces054 (allWordRows_cons forces055 (allWordRows_cons forces056 (allWordRows_cons forces057 (allWordRows_cons forces058 (allWordRows_cons forces059 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
